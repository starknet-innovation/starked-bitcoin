#!/usr/bin/env bash
# Every committed airs/*.json must equal its Lean export (docs/reference/ir.md § Regenerating).
# Run from anywhere: scripts/check_air_drift.sh [name...]   (default: every airs/*.json)
# Prints "<name> ok" or "<name> DRIFT (<export args>)"; exits 1 on any drift.
set -u
cd "$(dirname "$0")/../lean" || exit 2
LAKE=${LAKE:-lake}
names=("$@")
if [ ${#names[@]} -eq 0 ]; then for f in ../airs/*.json; do names+=("$(basename "$f" .json)"); done; fi
fail=0
for n in "${names[@]}"; do
  case $n in
    block_node_k[0-9]*)      args="block_node_k ${n#block_node_k}" ;;
    epoch_root_*_prev)       m=${n#epoch_root_}; args="epoch_root ${m%_prev} prev" ;;
    epoch_root_*)            args="epoch_root ${n#epoch_root_}" ;;
    epoch_join_*)            args="epoch_join ${n#epoch_join_}" ;;
    chain_seal_*_genesis)    m=${n#chain_seal_}; m=${m%_genesis}; args="chain_seal ${m//_/,} genesis" ;;
    chain_seal_*)            m=${n#chain_seal_}; args="chain_seal ${m//_/,}" ;;
    leafhash_*)              args="leafhash ${n#leafhash_}" ;;
    transcript_*)            args="transcript ${n#transcript_}" ;;
    channel_pow_check_*)     args="pow_check ${n#channel_pow_check_}" ;;
    channel_mix_qm31s_*)     args="channel mix_qm31s ${n#channel_mix_qm31s_}" ;;
    channel_mix_u32s_*)      args="channel mix_u32s ${n#channel_mix_u32s_}" ;;
    channel_*)               args="channel ${n#channel_}" ;;
    *)                       args="$n" ;;
  esac
  # shellcheck disable=SC2086
  if $LAKE env lean --run Export.lean $args 2>/dev/null | cmp -s - "../airs/$n.json"; then
    echo "$n ok"
  else
    echo "$n DRIFT ($args)"; fail=1
  fi
done
exit $fail
