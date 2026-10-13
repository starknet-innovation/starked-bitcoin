#!/bin/sh
# Chain survey on the node (docs/design/chain-survey.md): a 1-in-10 sample of every height, then all
# heights; resumable (rerun this script). Start detached:
#   cd ~/survey && setsid nohup ./survey_run.sh </dev/null >>run.log 2>&1 &
set -e
cd "$(dirname "$0")"
TO=$(cat tip.txt)
for STRIDE in 10 1; do
    sudo -n cat /data/bitcoin/.cookie | nice -n 19 ionice -c3 python3 -I survey_driver.py \
        --bin ./survey --out out --to "$TO" --chunk 1000 --workers 3 --stride "$STRIDE"
done
echo "survey complete $(date -u +%FT%TZ)"
