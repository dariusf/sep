#!/usr/bin/env bash
set -euo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cp "${EVOLVE_SEED:-Sep/Xsearch.lean}" evolve/initial_program.lean
export EVOLVE_STAGE1_DIRS="${EVOLVE_STAGE1_DIRS-qf_shls_entl}"
export EVOLVE_STAGE2_DIRS="${EVOLVE_STAGE2_DIRS-qf_shls_entl,qf_shid_entl}"
export EVOLVE_LLM_LOG_DIR="$PWD/evolve/out/llm"
export EVOLVE_LLM_WORKTREE="${EVOLVE_WORKTREE:-$PWD/.claude/worktrees/evolve}"
args=()
for a in "$@"; do
  if [ "$a" = "--resume" ]; then
    latest="$(ls -d evolve/out/checkpoints/checkpoint_* 2>/dev/null | sort -t_ -k2 -n | tail -1)"
    [ -n "$latest" ] || { echo "no checkpoint to resume from" >&2; exit 1; }
    args+=(--checkpoint "$latest")
  else
    args+=("$a")
  fi
done
exec python openevolve/openevolve-run.py \
  evolve/initial_program.lean \
  evolve/evaluator.py \
  --config evolve/config.yaml \
  --output evolve/out "${args[@]}"
