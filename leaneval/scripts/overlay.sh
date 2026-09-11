#!/bin/bash
# Copy this repo's lean-eval problem modules and manifests into a lean-eval checkout.
#
#   overlay.sh /path/to/lean-eval
#
# After overlaying:
#   lake build LeanEval.FormalConjectures.<Problem>      # typecheck one statement
#   lake exe lean-eval generate --problem <id>           # create generated/<id>/
#   cp -r submissions/<id>/Submission* generated/<id>/   # install our proof
#   cd generated/<id> && lake update && lake exe cache get && lake build && lake test
set -e
LE="${1:?usage: overlay.sh /path/to/lean-eval}"
HERE="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$LE/LeanEval/FormalConjectures" "$LE/manifests/problems"
cp "$HERE"/LeanEval/FormalConjectures/*.lean "$LE/LeanEval/FormalConjectures/"
cp "$HERE"/manifests/problems/*.toml "$LE/manifests/problems/"
echo "overlaid $(ls "$HERE"/LeanEval/FormalConjectures/*.lean | wc -l) modules and $(ls "$HERE"/manifests/problems/*.toml | wc -l) manifests into $LE"
