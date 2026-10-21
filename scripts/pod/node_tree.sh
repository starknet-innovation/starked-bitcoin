#!/usr/bin/env bash
# On the node: one epoch's recursion forest on a RunPod pod (cuda-epoch-tree), start to finish, as
# node_run.sh does for block proofs. The pod must exist and accept ~/.ssh/pod_ed25519. Steps: wait for
# ssh; tools; clone + build (bootstrap.sh without our block archive, then prove_tree.sh build) while
# the block proofs stream from this node; upload the tree proofs already made; launch prove_tree.sh;
# follow.sh into <local-dir> every 5 min; delete the pod at the END, when it stops answering, when the
# run fails twice, and at <deadline> (Unix time) whatever the state: the cost cap.
#   node_tree.sh <pod-id> <ssh-host> <ssh-port> <commit> <name> <from> <to> <proofs-dir> <headers.bin> \
#                <chain.sbchain> <local-dir> <deadline> [cuda-epoch-tree options]
# The pod assembles the forest (prove_tree.sh); <local-dir> gets forestk-<to>.bin, treevk.bin, tree/
# and logs/. Check it there with chainproof verify-epoch-wide (the coin sets live on this node). The RunPod API key is read from ~/.runpod_key and
# never printed or put on a command line. Log: <local-dir>/logs/node_tree.log.
set -uo pipefail
[ $# -ge 12 ] || { sed -n '2,12p' "$0"; exit 2; }
pod=$1 host=$2 port=$3 commit=$4 name=$5 from=$6 to=$7 pdir=$8 headers=$9 chain=${10} dst=${11} deadline=${12}
shift 12
here=$(cd "$(dirname "$0")" && pwd)
KEY=${RUNPOD_KEY_FILE:-$HOME/.runpod_key}
POD_SSH="ssh -i $HOME/.ssh/pod_ed25519 -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=3 -p $port root@$host"
read -r -a pod_ssh <<< "$POD_SSH"
rsh="${pod_ssh[*]:0:${#pod_ssh[@]}-1}"
mkdir -p "$dst/tree" "$dst/logs"
logf=$dst/logs/node_tree.log
log() { echo "$(date -u +%FT%TZ) $*" | tee -a "$logf"; }

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
  rsync -a --timeout=300 -e "$rsh" "root@$host:/workspace/$name/tree/" "$dst/tree/" 2>&1 | tail -2 | tee -a "$logf"
  rsync -a --timeout=120 -e "$rsh" "root@$host:/workspace/$name/treevk.bin" "root@$host:/workspace/$name/forestk-$to.bin" "$dst/" 2>&1 | tail -2 | tee -a "$logf"
  rsync -a --timeout=120 -e "$rsh" "root@$host:/workspace/logs/" "$dst/logs/pod/" 2>&1 | tail -2 | tee -a "$logf"
}
finish() {
  log "finish: $1"
  final_copy
  delete_pod "$1"
  log "local tree proofs: $(ls "$dst/tree" | wc -l)"
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

log "pod $pod ($host:$port), tree $from..$to, commit $commit, deadline $(date -u -d @"$deadline" +%FT%TZ)${FOLLOW_ONLY:+, re-attach}"
opts=("$@")
launch() { on_pod "cd /root/starked-bitcoin && (nohup scripts/pod/prove_tree.sh $name $from $to ${opts[*]} > /dev/null 2>&1 &)"; log "launched prove_tree.sh $name $from $to ${opts[*]}"; }
if [ -z "${FOLLOW_ONLY:-}" ]; then
for i in $(seq 1 40); do on_pod true 2> /dev/null && break; sleep 15; done
on_pod true || finish "no ssh after 10 min" 1
on_pod 'DEBIAN_FRONTEND=noninteractive apt-get update -qq > /dev/null && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq zstd rsync time > /dev/null && echo tools ok' 2>&1 | tee -a "$logf"
on_pod "nproc; cat /sys/fs/cgroup/cpu.max; free -g | sed -n 2p; nvidia-smi --query-gpu=name,memory.total --format=csv,noheader; df -h / /workspace | tail -2" 2>&1 | tee -a "$logf"

log "build (background on the pod) and the block proofs"
on_pod "rm -rf /root/starked-bitcoin; for i in 1 2 3; do git clone -q https://github.com/starknet-innovation/starked-bitcoin /root/starked-bitcoin && break; sleep 10; done; cd /root/starked-bitcoin && git checkout -q $commit && (CUDA_ARCH=sm_90 nohup bash -c 'NO_BUILD=1 scripts/pod/bootstrap.sh $commit && scripts/pod/prove_tree.sh build' > /root/build.out 2>&1 &)" 2>&1 | tee -a "$logf"
on_pod "mkdir -p /root/data/proofs /workspace/$name/tree"
n_local=$(ls "$pdir" | wc -l)
# The proofs go as one tar stream (10,000 files of ~1.2 MB), then are counted on the pod.
(cd "$pdir" && tar cf - --exclude='.*' .) | on_pod "tar xf - --no-same-owner -C /root/data/proofs" || finish "block proof transfer failed" 1
n_pod=$(on_pod "ls /root/data/proofs | wc -l")
rsync -a --no-owner --no-group --timeout=300 -e "$rsh" "$headers" "root@$host:/root/data/headers.bin" || finish "headers transfer failed" 1
rsync -a --no-owner --no-group --timeout=300 -e "$rsh" "$chain" "root@$host:/root/data/chain.sbchain" || finish "chain transfer failed" 1
log "block proofs: node $n_local, pod $n_pod"
[ "$n_pod" = "$n_local" ] || finish "block proof count differs" 1
rsync -a --no-owner --no-group --exclude=".*" --timeout=300 -e "$rsh" "$dst/tree/" "root@$host:/workspace/$name/tree/" || finish "tree proof upload failed" 1
[ -f "$dst/treevk.bin" ] && { rsync -a --no-owner --no-group -e "$rsh" "$dst/treevk.bin" "root@$host:/workspace/$name/" || finish "tree VK upload failed" 1; }
log "tree proofs on the pod: $(on_pod "ls /workspace/$name/tree | wc -l")"

for i in $(seq 1 160); do
  st=$(on_pod "grep -c 'TREE BUILD DONE' /root/build.out; pgrep -f '[p]rove_tree.sh build|[b]ootstrap.sh' > /dev/null && echo running || echo stopped" 2> /dev/null | tr '\n' ' ')
  case $st in 1*) break ;; 0\ stopped*) on_pod "tail -20 /root/build.out" | tee -a "$logf"; finish "build failed" 1 ;; esac
  sleep 30
done
case $st in 1*) log "build done" ;; *) finish "build not done after 80 min" 1 ;; esac
launch
sleep 60
fi
relaunched=0
while true; do
  POD_SSH="$POD_SSH" WORK=/workspace SUBDIR=tree PROC=cuda-epoch-tree INTERVAL=${INTERVAL:-300} "$here/follow.sh" "$name" "$dst" >> "$dst/logs/follow.log" 2>&1
  rc=$?
  log "follow.sh exit $rc: $(tail -1 "$dst/logs/follow.log")"
  case $rc in
    0) break ;;
    4) if [ "$relaunched" = 0 ]; then relaunched=1; launch; sleep 60; continue; fi
       finish "cuda-epoch-tree stopped twice without END" 1 ;;
    *) finish "pod unreachable (follow.sh exit $rc)" 1 ;;
  esac
done
log "status: $(on_pod "tail -2 /workspace/logs/$name.status" | tr '\n' ' ')"
log "end: $(on_pod "grep -E 'TREE DONE|FAILED|error' /workspace/logs/$name.log | tail -2" | tr '\n' ' ')"
on_pod "ls -l /workspace/$name/forestk-$to.bin" 2>&1 | tee -a "$logf"
finish "run ended"
