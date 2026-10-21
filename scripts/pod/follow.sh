#!/usr/bin/env bash
# On the Mac: follow a prove_epoch.sh run. Every INTERVAL seconds (default 300) it copies the new proofs
# and the logs off the pod and prints one progress line; a pod that stops answering is reported within
# two intervals instead of being noticed hours later.
#   follow.sh <name> <local-dir>       (POD_SSH: the pod's ssh command, e.g. "ssh -p 18735 root@1.2.3.4")
# Exits 0 when the run's status has END, 3 when the pod has not answered MISSES (default 2) times in a
# row, 4 when the cuda-epoch process is gone without END (the container restarted: relaunch
# prove_epoch.sh, it resumes). A desktop notification accompanies 3 and 4 (macOS).
set -uo pipefail
name=${1:?usage: follow.sh <name> <local-dir>}
dst=${2:?local dir}
: "${POD_SSH:?set POD_SSH to the ssh command of the pod}"
interval=${INTERVAL:-300}
misses_max=${MISSES:-2}
WORK=${WORK:-/workspace}
sub=${SUBDIR:-proofs}
proc_name=${PROC:-cuda-epoch}
mkdir -p "$dst/$sub" "$dst/logs"
read -r -a ssh_cmd <<< "$POD_SSH"
# rsync's -e takes the ssh command without the destination (the last word).
dest=${ssh_cmd[*]: -1}
# Dead connections are dropped by ssh itself (macOS has no `timeout`): ~45 s without a keepalive reply.
opts="-o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=3"
n_words=${#ssh_cmd[@]}
ssh_pre="${ssh_cmd[*]:0:n_words-1}"
rsh="$ssh_pre $opts"
alert() {
  echo "ALERT $(date -u +%T): $1"
  command -v osascript > /dev/null && osascript -e "display notification \"$1\" with title \"prove_epoch $name\"" 2> /dev/null
}
# On the pod: the proof count, whether cuda-epoch runs, and whether the status has END.
probe="echo \$(ls $WORK/$name/$sub 2>/dev/null | wc -l) \$(pgrep -x '$proc_name' > /dev/null && echo up || echo down) \$(grep -c ^END $WORK/logs/$name.status 2>/dev/null)"
misses=0
while true; do
  st=$($ssh_pre $opts "$dest" "$probe" 2> /dev/null)
  if [ -z "$st" ]; then
    misses=$((misses + 1))
    echo "$(date -u +%T) no answer from the pod ($misses/$misses_max)"
    if [ "$misses" -ge "$misses_max" ]; then alert "the pod has not answered for $misses checks"; exit 3; fi
    sleep "$interval"; continue
  fi
  misses=0
  read -r n proc ends <<< "$st"
  rsync -a --timeout=300 -e "$rsh" "$dest:$WORK/$name/$sub/" "$dst/$sub/" || echo "  rsync of $sub failed (rc $?)"
  rsync -a --timeout=120 -e "$rsh" "$dest:$WORK/logs/$name.*" "$dst/logs/" || echo "  rsync of logs failed (rc $?)"
  last=$(tail -1 "$dst/logs/$name.log" 2> /dev/null | cut -c1-80)
  echo "$(date -u +%T) pod $n $sub, $proc_name $proc; local $(ls "$dst/$sub" | wc -l); last: $last"
  if [ "${ends:-0}" -gt 0 ] && [ "$proc" = down ]; then echo "END: $(tail -3 "$dst/logs/$name.status" | tr '\n' ' ')"; exit 0; fi
  if [ "$proc" = down ]; then alert "$proc_name is not running and the run has not ended"; exit 4; fi
  sleep "$interval"
done
