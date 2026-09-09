#!/bin/bash
# Summarise the last build: per-problem Solution/Comparator state and the axioms
# each comparator's `fc_statement_is_proved` depends on.
source "$(dirname "$0")/lakeenv.sh"
LOG="${1:-/state/partition1/job-17251809/claude-3689738/-scratch-nnp5656-projects-fc/e4593cf7-bf38-4d0b-a7be-680b8ef1fc8d/scratchpad/av-logs}/all.log"
OLEAN="$FC/.lake/build/lib/lean/AtlasVerified"
printf "%-13s %-9s %-11s %s\n" PROBLEM SOLUTION COMPARATOR AXIOMS
printf "%-13s %-9s %-11s %s\n" ------- -------- ---------- ------
for d in Erdos138 Erdos337 Green25 OeisA108081 OeisA211417 OeisA22030 Oqp35 Wotw100 Wotw314; do
  sol="FAIL"; cmp="FAIL"
  [ -f "$OLEAN/$d/Solution.olean" ]   && sol="ok"
  [ -f "$OLEAN/$d/Comparator.olean" ] && cmp="ok"
  ax=$(grep -oE "'AtlasCompare\.$d\.fc_statement_is_proved' depends on axioms: \[[^]]*\]" "$LOG" \
       | sed 's/.*axioms: //' | tail -1)
  [ -z "$ax" ] && ax="-"
  printf "%-13s %-9s %-11s %s\n" "$d" "$sol" "$cmp" "$ax"
done
echo
echo "remaining errors:"
grep -E "^error: AtlasVerified" "$LOG" | sed 's#error: AtlasVerified/#  #' | sort | uniq -c || echo "  none"
