#!/usr/bin/env bash
# One epoch's block proofs on a pod with cuda-epoch, resumable.
#   prove_epoch.sh <name> <from> <to> [cuda-epoch options, e.g. --skip <list> | --only <list>]
# Inputs (scripts/pod/xfer_epoch.sh puts them there): $DATA/headers.bin, $DATA/chain.sbchain,
# $DATA/set-<from-1>.bin, $DATA/blocks/<h>.bin, $DATA/undo/<h>.{undo,ctx}.
# Outputs on the persistent volume: $WORK/<name>/proofs/<h>.sbblock and set-<to>.bin, and in $LOGS
# <name>.log (one line per block), <name>.status (START, END, exit code, peaks) and <name>.smi.csv.
# Always passes --resume: run it again after an interruption and it proves only the missing blocks
# (each proof file is written atomically). Detach it from the ssh session:
#   nohup scripts/pod/prove_epoch.sh e945000 935001 945000 --skip skip.txt > /dev/null 2>&1 &
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
name=${1:?usage: prove_epoch.sh <name> <from> <to> [options]}
from=${2:?from}
to=${3:?to}
shift 3
dir=$WORK/$name
mkdir -p "$dir" "$LOGS"
ln -sfn "$DATA/blocks" "$dir/blocks"
ln -sfn "$DATA/undo" "$dir/undo"
bin=$SRC/zig-out/bin/cuda-epoch
log=$LOGS/$name.log
# Keep the logs of earlier attempts.
[ -s "$log" ] && mv "$log" "$log.$(date -u +%Y%m%dT%H%M%S)"
date -u +"START %FT%TZ $from..$to $*" >> "$LOGS/$name.status"
nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 1000 >> "$LOGS/$name.smi.csv" &
smi=$!
/usr/bin/time -v "$bin" "$DATA/headers.bin" "$dir" "$to" "$DATA/chain.sbchain" --from "$from" "$DATA/set-$((from - 1)).bin" --resume "$@" > "$log" 2>&1
rc=$?
kill $smi 2>/dev/null; wait $smi 2>/dev/null
util=$(awk -F', ' '{gsub(/ %/,"",$3); s+=$3; n++} END {if (n) printf "%.1f", s/n}' "$LOGS/$name.smi.csv")
peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2+0>m) m=$2+0} END {print m}' "$LOGS/$name.smi.csv")
{
  date -u +"END %FT%TZ exit $rc"
  echo "proofs $(ls "$dir/proofs" | wc -l); mean GPU util ${util}%; peak GPU memory ${peak} MiB; host peak RSS $(grep 'Maximum resident' "$log" | awk '{print $NF}') kB"
  [ -f "$dir/deferred-$to.txt" ] && echo "deferred (device memory): $(tr '\n' ' ' < "$dir/deferred-$to.txt")"
} >> "$LOGS/$name.status"
exit $rc
