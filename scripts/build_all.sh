#!/bin/bash
# Build every AtlasVerified module in ONE lake invocation so lake's own scheduler
# parallelises across them (separate invocations would serialise on the build lock).
source "$(dirname "$0")/lakeenv.sh"
LOG="${1:-$REPO/build-logs}"
shift
mkdir -p "$LOG"
"$(dirname "$0")/sync.sh"
cd "$FC" || exit 1
TARGETS=()
if [ $# -gt 0 ]; then for m in "$@"; do TARGETS+=("AtlasVerified.$m"); done
else
  for d in Erdos138 Erdos337 Green25 OeisA108081 OeisA211417 OeisA22030 Oqp35 Wotw100 Wotw314; do
    [ -f "$REPO/AtlasVerified/$d/Solution.lean" ]   && TARGETS+=("AtlasVerified.$d.Solution")
    [ -f "$REPO/AtlasVerified/$d/Comparator.lean" ] && TARGETS+=("AtlasVerified.$d.Comparator")
  done
fi
echo "===== targets: ${TARGETS[*]}"
echo "===== start $(date +%H:%M:%S)"
lake build "${TARGETS[@]}" > "$LOG/all.log" 2>&1
echo "LAKE_EXIT=$?"
echo "===== per-file errors ====="
grep -oE "AtlasVerified/[A-Za-z0-9]+/[A-Za-z]+\.lean:[0-9]+:[0-9]+: error" "$LOG/all.log" \
  | sed 's#AtlasVerified/##' | sort | uniq -c | sort -rn
echo "===== files with zero errors ====="
for d in Erdos138 Erdos337 Green25 OeisA108081 OeisA211417 OeisA22030 Oqp35 Wotw100 Wotw314; do
  n=$(grep -cE "AtlasVerified/$d/[A-Za-z]+\.lean:[0-9]+:[0-9]+: error" "$LOG/all.log")
  printf "%-14s errors=%s\n" "$d" "$n"
done
echo "===== done $(date +%H:%M:%S)"
