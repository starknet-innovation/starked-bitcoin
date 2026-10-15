#!/bin/sh
# Full-chain replay on the node (docs/design/block-data.md § Full-chain data): raw blocks streamed from
# the local node (read-only RPC, the node's cookie on stdin, kept in memory) into `replay`. Writes, in
# ./out, the coin sets at Core's assumeUTXO heights (compare hash_serialized with chainparams.cpp), a
# checkpoint set every 100,000 blocks, and the rehearsal window's blocks, undo and ctx with its
# previous set. Start detached:
#   cd ~/replay && setsid nohup ./replay_run.sh </dev/null >>run.log 2>&1 &
# Resume after a stop: FROM=<h+1> SET=out/set-<h>.bin ./replay_run.sh (h a checkpoint).
set -e
cd "$(dirname "$0")"
TO=${TO:-970000}
FROM=${FROM:-0}
RESUME=""
[ "$FROM" -gt 0 ] && RESUME="--from $FROM ${SET:?SET=out/set-<FROM-1>.bin}"
echo "replay $FROM..$TO start $(date -u +%FT%TZ)"
sudo -n cat /data/bitcoin/.cookie | nice -n 19 ionice -c3 python3 -I stream_blocks.py --cookie-stdin \
    --url http://127.0.0.1:8332 --headers headers.bin --batch 8 --workers 4 "$FROM" "$TO" 2>>stream.log \
  | nice -n 19 ./replay headers.bin out $RESUME --capacity 200000000 --set-every 100000 \
      --set-at 840000 --set-at 880000 --set-at 910000 --set-at 935000 --set-at 960000 \
      --window 960001 970000
echo "replay complete $(date -u +%FT%TZ)"
