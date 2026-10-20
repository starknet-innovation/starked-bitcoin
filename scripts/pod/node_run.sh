#!/usr/bin/env bash
# On the node: one epoch run on a RunPod pod, start to finish, without the Mac. The pod must exist and
# accept ~/.ssh/pod_ed25519 (its public key in the pod's PUBLIC_KEY). Steps: wait for ssh; install zstd
# and rsync; bootstrap (clone + build) while the inputs stream from this node (xfer_epoch.sh); upload the
# proofs already made; launch prove_epoch.sh (--resume); follow.sh into <local-dir> every 5 min; at the
# END compare the pod's final set with <check-set>; delete the pod. The pod is also deleted when it stops
# answering, when the run fails twice, and at <deadline> (Unix time) whatever the state: the cost cap.
#   node_run.sh <pod-id> <ssh-host> <ssh-port> <commit> <name> <from> <to> <set-dir> <blocks-dir> \
#               <chain> <local-dir> <check-set> <deadline> [cuda-epoch options]
# SKIP: heights to pass as --skip (space-separated). The RunPod API key is read from ~/.runpod_key and
# never printed or put on a command line. Log: <local-dir>/logs/node_run.log. FOLLOW_ONLY=1 re-attaches to
# a run already proving (e.g. after this node restarted): no setup, no launch, straight to following.
set -uo pipefail
[ $# -ge 13 ] || { sed -n '2,12p' "$0"; exit 2; }
pod=$1 host=$2 port=$3 commit=$4 name=$5 from=$6 to=$7 setdir=$8 bdir=$9 chain=${10} dst=${11} check=${12} deadline=${13}
shift 13
here=$(cd "$(dirname "$0")" && pwd)
KEY=${RUNPOD_KEY_FILE:-$HOME/.runpod_key}
POD_SSH="ssh -i $HOME/.ssh/pod_ed25519 -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=3 -p $port root@$host"
read -r -a pod_ssh <<< "$POD_SSH"
mkdir -p "$dst/proofs" "$dst/logs"
logf=$dst/logs/node_run.log
log() { echo "$(date -u +%FT%TZ) $*" | tee -a "$logf"; }

# The key goes to curl on stdin (a config line), not on its command line.
api() {
  local method=$1 path=$2
  shift 2
  printf 'header = "Authorization: Bearer %s"\n' "$(cat "$KEY")" | curl -sS -K - -X "$method" "https://rest.runpod.io/v1$path" "$@"
}
delete_pod() {
  local code i
  for i in 1 2 3 4 5 6; do
    code=$(api DELETE "/pods/$pod" -o /dev/null -w '%{http_code}')
    log "delete pod $pod: HTTP $code ($1)"
    case $code in 2??|404) return 0 ;; esac
    sleep 20
  done
  log "DELETE FAILED: delete pod $pod by hand"
  return 1
}
final_copy() {
  rsync -a --timeout=300 -e "${pod_ssh[*]:0:${#pod_ssh[@]}-1}" "root@$host:/workspace/$name/proofs/" "$dst/proofs/" 2>&1 | tail -2 | tee -a "$logf"
  rsync -a --timeout=120 -e "${pod_ssh[*]:0:${#pod_ssh[@]}-1}" "root@$host:/workspace/logs/" "$dst/logs/pod/" 2>&1 | tail -2 | tee -a "$logf"
}
finish() {
  log "finish: $1"
  final_copy
  delete_pod "$1"
  log "local proofs: $(ls "$dst/proofs" | wc -l)"
  exit "${2:-0}"
}
on_pod() { "${pod_ssh[@]}" "$@"; }

# The cost cap: delete the pod at the deadline, whatever this script is doing.
(
  while [ "$(date +%s)" -lt "$deadline" ]; do sleep 30; done
  log "deadline reached"
  final_copy
  delete_pod deadline
  kill -TERM $$ 2> /dev/null
) &
cap=$!
trap 'kill $cap 2> /dev/null' EXIT
trap 'log "stopped (deadline or signal)"; exit 5' TERM INT

log "pod $pod ($host:$port), epoch $from..$to, commit $commit, deadline $(date -u -d @"$deadline" +%FT%TZ)${FOLLOW_ONLY:+, re-attach}"
opts=("$@")
if [ -n "${SKIP:-}" ]; then opts+=(--skip /root/data/skip.txt); fi
launch() { on_pod "cd /root/starked-bitcoin && (nohup scripts/pod/prove_epoch.sh $name $from $to ${opts[*]} > /dev/null 2>&1 &)"; log "launched prove_epoch.sh $name $from $to ${opts[*]}"; }
if [ -z "${FOLLOW_ONLY:-}" ]; then
for i in $(seq 1 40); do on_pod true 2> /dev/null && break; sleep 15; done
on_pod true || finish "no ssh after 10 min" 1
on_pod 'DEBIAN_FRONTEND=noninteractive apt-get update -qq > /dev/null && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq zstd rsync time > /dev/null && echo tools ok' 2>&1 | tee -a "$logf"
on_pod "nproc; cat /sys/fs/cgroup/cpu.max; free -g | sed -n 2p; nvidia-smi --query-gpu=name,memory.total --format=csv,noheader; df -h / /workspace | tail -2" 2>&1 | tee -a "$logf"

log "bootstrap (background on the pod) and transfer"
on_pod "rm -rf /root/starked-bitcoin; for i in 1 2 3; do git clone -q https://github.com/starknet-innovation/starked-bitcoin /root/starked-bitcoin && break; sleep 10; done; cd /root/starked-bitcoin && git checkout -q $commit && (CUDA_ARCH=sm_90 nohup scripts/pod/bootstrap.sh $commit > /root/bootstrap.out 2>&1 &)" 2>&1 | tee -a "$logf"
NODE_SSH="bash -c" POD_SSH="$POD_SSH" DATA=/root/data "$here/xfer_epoch.sh" "$from" "$to" "$setdir" "$bdir" "$chain" 2>&1 | tee -a "$logf"
[ "${PIPESTATUS[0]}" = 0 ] || finish "transfer failed" 1
on_pod "mkdir -p /workspace/$name/proofs"
rsync -a --no-owner --no-group --exclude=".*" --timeout=300 -e "${pod_ssh[*]:0:${#pod_ssh[@]}-1}" "$dst/proofs/" "root@$host:/workspace/$name/proofs/" || finish "proof upload failed" 1
log "proofs on the pod: $(on_pod "ls /workspace/$name/proofs | wc -l")"

for i in $(seq 1 120); do
  st=$(on_pod "grep -c 'BOOTSTRAP DONE' /root/bootstrap.out; pgrep -f '[b]ootstrap.sh' > /dev/null && echo running || echo stopped" 2> /dev/null | tr '\n' ' ')
  case $st in 1*) break ;; 0\ stopped*) on_pod "tail -20 /root/bootstrap.out" | tee -a "$logf"; finish "bootstrap failed" 1 ;; esac
  sleep 30
done
case $st in 1*) log "bootstrap done" ;; *) finish "bootstrap not done after 60 min" 1 ;; esac

[ -n "${SKIP:-}" ] && on_pod "printf '%s\n' $SKIP > /root/data/skip.txt"
launch
sleep 60
fi
relaunched=0
while true; do
  POD_SSH="$POD_SSH" WORK=/workspace INTERVAL=${INTERVAL:-300} "$here/follow.sh" "$name" "$dst" >> "$dst/logs/follow.log" 2>&1
  rc=$?
  log "follow.sh exit $rc: $(tail -1 "$dst/logs/follow.log")"
  case $rc in
    0) break ;;
    4) if [ "$relaunched" = 0 ]; then relaunched=1; launch; sleep 60; continue; fi
       finish "cuda-epoch stopped twice without END" 1 ;;
    *) finish "pod unreachable (follow.sh exit $rc)" 1 ;;
  esac
done

status=$(on_pod "tail -4 /workspace/logs/$name.status")
log "status: $(echo "$status" | tr '\n' ' ')"
a=$(on_pod "sha256sum < /workspace/$name/set-$to.bin" | cut -c1-64)
b=$(sha256sum < "$check" | cut -c1-64)
log "set-$to.bin: pod $a, $check $b: $([ "$a" = "$b" ] && echo SAME || echo DIFFER)"
finish "run ended"
