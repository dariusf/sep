#!/usr/bin/env bash
set -euo pipefail

MAIN="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WT="${EVOLVE_WORKTREE:-$MAIN/.claude/worktrees/evolve}"

if [ ! -d "$WT" ]; then
  mkdir -p "$(dirname "$WT")"
  git -C "$MAIN" worktree add --detach "$WT" HEAD
else
  git -C "$WT" checkout --detach "$(git -C "$MAIN" rev-parse HEAD)"
fi

mkdir -p "$WT/.lake"
if [ ! -e "$WT/.lake/packages" ]; then
  ln -s "$MAIN/.lake/packages" "$WT/.lake/packages"
fi

mkdir -p "$WT/sl-comp-bench"
for d in "$MAIN"/sl-comp-bench/*; do
  b="$(basename "$d")"
  [ -e "$WT/sl-comp-bench/$b" ] || ln -s "$d" "$WT/sl-comp-bench/$b"
done

cd "$WT"
lake build bench # compile the driver exe
echo "worktree ready: $WT"
