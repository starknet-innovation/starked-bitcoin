#!/usr/bin/env bash
# On the Mac: an epoch's inputs from the node (scripts/replay_run.sh's /data/replay) to a pod, streamed
# through this machine with zstd; nothing is written on the node. Four streams: the previous set in two
# halves and the blocks with their undo and ctx in two halves; then headers.bin and the chain proof.
#   xfer_epoch.sh <from> <to> <set-dir> <blocks-dir> <chain.sbchain>
#     set-dir:    the node's directory holding set-<from-1>.bin (e.g. /data/replay/out)
#     blocks-dir: the node's directory holding blocks/ and undo/ (e.g. /data/replay/out935)
# NODE_SSH and POD_SSH: the ssh commands of the node and the pod. Fills the pod's $DATA (default
# /root/data, scripts/pod/env.sh) and checks every file's sha256 against the node's.
set -euo pipefail
from=${1:?usage: xfer_epoch.sh <from> <to> <set-dir> <blocks-dir> <chain.sbchain>}
to=${2:?to}
setdir=${3:?set dir}
bdir=${4:?blocks dir}
chain=${5:?chain proof}
: "${NODE_SSH:?set NODE_SSH}" "${POD_SSH:?set POD_SSH}"
DATA=${DATA:-/root/data}
read -r -a node <<< "$NODE_SSH"
read -r -a pod <<< "$POD_SSH"
set_file=$setdir/set-$((from - 1)).bin
size=$("${node[@]}" "stat -c %s $set_file")
half=$((size / 2))
mid=$(( (from + to) / 2 ))
"${pod[@]}" "mkdir -p $DATA/blocks $DATA/undo && rm -f $DATA/set-$((from - 1)).bin"
date -u +"start %FT%TZ"
( "${node[@]}" "head -c $half $set_file | zstd -q -T2 -13 -c" | "${pod[@]}" "zstd -q -d -c | dd of=$DATA/set-$((from - 1)).bin bs=4M iflag=fullblock conv=notrunc status=none" ) &
( "${node[@]}" "tail -c +$((half + 1)) $set_file | zstd -q -T2 -13 -c" | "${pod[@]}" "zstd -q -d -c | dd of=$DATA/set-$((from - 1)).bin bs=4M iflag=fullblock oflag=seek_bytes seek=$half conv=notrunc status=none" ) &
for r in "$from $mid" "$((mid + 1)) $to"; do
  set -- $r
  ( "${node[@]}" "cd $bdir && for h in \$(seq $1 $2); do echo blocks/\$h.bin; echo undo/\$h.undo; echo undo/\$h.ctx; done | tar cf - -T - | zstd -q -T2 -13 -c" | "${pod[@]}" "zstd -q -d -c | tar xf - -C $DATA --no-same-owner" ) &
done
wait
"${node[@]}" "cat $(dirname "$setdir")/headers.bin" | "${pod[@]}" "cat > $DATA/headers.bin"
"${pod[@]}" "cat > $DATA/chain.sbchain" < "$chain"
date -u +"copied %FT%TZ; checking"
list="for h in \$(seq $from $to); do cat blocks/\$h.bin undo/\$h.undo undo/\$h.ctx; done | sha256sum"
a=$("${node[@]}" "cd $bdir && $list; sha256sum < $set_file; sha256sum < $(dirname "$setdir")/headers.bin")
b=$("${pod[@]}" "cd $DATA && $list; sha256sum < set-$((from - 1)).bin; sha256sum < headers.bin")
c=$(shasum -a 256 < "$chain" | cut -d' ' -f1)
d=$("${pod[@]}" "sha256sum < $DATA/chain.sbchain" | cut -d' ' -f1)
echo "node: $(echo "$a" | cut -c1-16 | tr '\n' ' ')"
echo "pod:  $(echo "$b" | cut -c1-16 | tr '\n' ' ')"
[ "$a" = "$b" ] && [ "$c" = "$d" ] && echo "SAME: blocks, undo, ctx, set-$((from - 1)).bin, headers.bin, chain proof" || { echo "DIFFER"; exit 1; }
