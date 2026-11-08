#!/bin/sh
# Smoke-run the fast demos listed in scripts/smoke.txt (one per area).
# Run from the repository root or lean/: CI and local runs use the same list.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/lean"
grep -v '^#' "$root/scripts/smoke.txt" | grep -v '^[[:space:]]*$' | while read -r exe; do
  echo "== lake exe $exe =="
  lake exe "$exe"
done
echo SMOKE_ALL_DONE
