#!/usr/bin/env bash
# On the node: two or more proven epochs joined into one chain proof (chainproof prove-chain) on a
# RunPod pod, start to finish. The pod must exist and accept ~/.ssh/pod_ed25519. Steps: wait for ssh;
# tools; clone <commit> (+ PATCH) and build chainproof (CPU); upload each epoch's forest, tree VK and one
# block proof per size key (all prove-chain reads), the chain proof, and any root files already made;
# run prove-chain; copy <out> back; delete the pod at the end, on failure, and at <deadline> whatever
# the state (the cost cap).
#   node_join.sh <pod-id> <ssh-host> <ssh-port> <commit> <out-dir> <chain.sbchain> <deadline> <epoch>...
# Each <epoch> is `<dir>:<to>:<from>:<prev-hex|->:<fin-hex>` (the sets' Blake2s digests: the pod never
# sees a set); <dir> holds forestk-<to>.bin, treevk.bin, and proofs/ (or set PROOFS_<to>=<dir> for the
# block proofs). Root files in <out-dir> (root-<to>.bin) are uploaded and reused when at the chain's
# root shape. PATCH: a `git format-patch` file applied on top of <commit>. The RunPod API key is read
# from ~/.runpod_key, never printed. Log: <out-dir>/node_join.log.
set -uo pipefail
[ $# -ge 9 ] || { sed -n '2,14p' "$0"; exit 2; }
pod=$1 host=$2 port=$3 commit=$4 out=$5 chain=$6 deadline=$7
shift 7
epochs=("$@")
KEY=${RUNPOD_KEY_FILE:-$HOME/.runpod_key}
POD_SSH="ssh -i $HOME/.ssh/pod_ed25519 -o StrictHostKeyChecking=accept-new -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=3 -p $port root@$host"
read -r -a pod_ssh <<< "$POD_SSH"
rsh="${pod_ssh[*]:0:${#pod_ssh[@]}-1}"
mkdir -p "$out"
logf=$out/node_join.log
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
on_pod() { "${pod_ssh[@]}" "$@"; }
final_copy() {
  rsync -a --timeout=300 -e "$rsh" "root@$host:/workspace/join/out/" "$out/" 2>&1 | tail -2 | tee -a "$logf"
}
finish() {
  log "finish: $1"
  final_copy
  delete_pod "$1"
  exit "${2:-0}"
}
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

log "pod $pod ($host:$port), ${#epochs[@]} epochs, commit $commit, deadline $(date -u -d @"$deadline" +%FT%TZ)"
for i in $(seq 1 40); do on_pod true 2> /dev/null && break; sleep 15; done
on_pod true || finish "no ssh after 10 min" 1
on_pod 'DEBIAN_FRONTEND=noninteractive apt-get update -qq > /dev/null && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq git curl xz-utils rsync time > /dev/null && echo tools ok' 2>&1 | tee -a "$logf"
on_pod "nproc; free -g | sed -n 2p; df -h / /workspace | tail -2" 2>&1 | tee -a "$logf"
apply=true
if [ -n "${PATCH:-}" ]; then
  on_pod "cat > /root/fix.patch" < "$PATCH" || finish "patch upload failed" 1
  apply="git -c user.email=pod@local -c user.name=pod am -q /root/fix.patch && git log --oneline -1"
fi
# CPU only: Zig 0.15.2 (as bootstrap.sh, which needs a GPU), the submodules, then chainproof.
on_pod "cat > /root/build.sh" <<EOF2 || finish "build script upload failed" 1
set -euo pipefail
mkdir -p /root/zig
if ! /root/zig/zig version 2>/dev/null | grep -q '^0.15.2\$'; then
  case \$(uname -m) in
    x86_64) t=zig-x86_64-linux-0.15.2.tar.xz; sum=02aa270f183da276e5b5920b1dac44a63f1a49e55050ebde3aecc9eb82f93239 ;;
    aarch64) t=zig-aarch64-linux-0.15.2.tar.xz; sum=958ed7d1e00d0ea76590d27666efbf7a932281b3d7ba0c6b01b0ff26498f667f ;;
  esac
  curl -fsSL -o /tmp/\$t https://ziglang.org/download/0.15.2/\$t
  echo "\$sum  /tmp/\$t" | sha256sum -c -
  tar xf /tmp/\$t --no-same-owner -C /root/zig --strip-components=1
fi
rm -rf /root/starked-bitcoin
for i in 1 2 3; do git clone -q https://github.com/starknet-innovation/starked-bitcoin /root/starked-bitcoin && break; sleep 10; done
cd /root/starked-bitcoin && git checkout -q $commit
for i in 1 2 3 4; do git submodule update -q --init --recursive && break; sleep 10; done
$apply
/root/zig/zig build -Doptimize=ReleaseFast -p zig-out-cpu
ls -l zig-out-cpu/bin/chainproof
echo JOIN BUILD DONE
EOF2
on_pod "(nohup bash /root/build.sh > /root/build.out 2>&1 &)"
log "build started on the pod"

# The inputs: per epoch its forest, tree VK and the first block proof of each size key.
specs=()
on_pod "mkdir -p /workspace/join/out /root/data" || finish "mkdir failed" 1
for e in "${epochs[@]}"; do
  IFS=: read -r dir to from prev fin <<< "$e"
  pdir=${dir}/proofs
  v="PROOFS_$to"; [ -n "${!v:-}" ] && pdir=${!v}
  firsts=$(python3 -I - "$dir/forestk-$to.bin" <<'EOF'
import struct, sys
b = open(sys.argv[1], 'rb').read()
assert b[:8] == b'SBFORSTK'
frm, to = struct.unpack_from('<II', b, 12)
n = struct.unpack_from('<Q', b, 20)[0]
logs = b[28:28 + n]
assert n == to - frm + 1
seen = {}
for i, l in enumerate(logs):
    seen.setdefault(l, frm + i)
print(' '.join(str(h) for h in sorted(seen.values())))
EOF
) || finish "forest $dir/forestk-$to.bin unreadable" 1
  log "epoch $from..$to: first proofs per size key: $firsts"
  on_pod "mkdir -p /root/data/e$to/proofs"
  rsync -a --no-owner --no-group --timeout=300 -e "$rsh" "$dir/forestk-$to.bin" "$dir/treevk.bin" "root@$host:/root/data/e$to/" || finish "epoch $to upload failed" 1
  for h in $firsts; do
    rsync -a --no-owner --no-group --timeout=300 -e "$rsh" "$pdir/$h.sbblock" "root@$host:/root/data/e$to/proofs/" || finish "proof $h upload failed" 1
  done
  [ -f "$out/root-$to.bin" ] && { rsync -a --no-owner --no-group -e "$rsh" "$out/root-$to.bin" "root@$host:/workspace/join/out/" || finish "root upload failed" 1; }
  if [ "$from" = 0 ]; then specs+=("/root/data/e$to:$to#-,$fin"); else specs+=("/root/data/e$to:$to:$from:not-read#$prev,$fin"); fi
done
rsync -a --no-owner --no-group --timeout=300 -e "$rsh" "$chain" "root@$host:/root/data/chain.sbchain" || finish "chain transfer failed" 1
log "inputs uploaded; specs: ${specs[*]}"

for i in $(seq 1 120); do
  st=$(on_pod "grep -c 'JOIN BUILD DONE' /root/build.out; pgrep -f '[b]uild.sh|[z]ig build' > /dev/null && echo running || echo stopped" 2> /dev/null | tr '\n' ' ')
  case $st in 1*) break ;; 0\ stopped*) on_pod "tail -20 /root/build.out" | tee -a "$logf"; finish "build failed" 1 ;; esac
  sleep 30
done
case $st in 1*) log "build done" ;; *) finish "build not done after 60 min" 1 ;; esac

on_pod "cd /root/starked-bitcoin && (nohup /usr/bin/time -v zig-out-cpu/bin/chainproof prove-chain vk/mainnet-q70-p26-l20.vk /root/data/chain.sbchain /workspace/join/out ${specs[*]} > /workspace/join/prove-chain.log 2>&1; echo \"EXIT \$?\" >> /workspace/join/prove-chain.log) > /dev/null 2>&1 &"
log "launched prove-chain"
miss=0
while true; do
  sleep 300
  st=$(on_pod "tail -c 400 /workspace/join/prove-chain.log | tr '\n' ' '; echo; free -g | sed -n 2p" 2> /dev/null) || { miss=$((miss + 1)); log "no answer ($miss)"; [ $miss -ge 6 ] && finish "pod unreachable" 1; continue; }
  miss=0
  log "$(echo "$st" | tail -c 500 | tr '\n' ' ')"
  case $st in *"EXIT "*) break ;; esac
done
on_pod "cp /workspace/join/prove-chain.log /workspace/join/out/" 2>&1 | tee -a "$logf"
on_pod "grep -E 'EXIT|join |Maximum resident|Elapsed' /workspace/join/prove-chain.log" 2>&1 | tee -a "$logf"
finish "run ended"
