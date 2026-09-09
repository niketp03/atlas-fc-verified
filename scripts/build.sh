#!/bin/bash
# Usage: build.sh <logdir> <module> [<module> ...]
# Builds each module sequentially, writing <logdir>/<module>.log and a summary.
source "$(dirname "$0")/lakeenv.sh"
LOG="$1"; shift
mkdir -p "$LOG"
cd "$FC" || exit 1
for m in "$@"; do
  echo "===== BUILD $m start $(date +%H:%M:%S) ====="
  lake build "AtlasVerified.$m" > "$LOG/$m.log" 2>&1
  rc=$?
  echo "$m EXIT=$rc"
  grep -E "AtlasVerified/.*\.lean:[0-9]+:[0-9]+: error" "$LOG/$m.log" | head -8
done
echo "===== DONE $(date +%H:%M:%S) ====="
