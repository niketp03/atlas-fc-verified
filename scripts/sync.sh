#!/bin/bash
# Copy this repo's Lean sources into the formal-conjectures checkout.
#
# Two payloads:
#   AtlasVerified/      -> $FC/AtlasVerified/            (own lean_lib, see lakefile patch)
#   Green25Improved/    -> $FC/FormalConjectures/GreensOpenProblems/
#
# The Green25Improved modules are FormalConjectures-namespace modules (they import
# `FormalConjectures.GreensOpenProblems.«25»` and extend it), so they have to live
# inside the FC library rather than alongside AtlasVerified. They additionally need
# `formal-conjectures.patch` applied to the checkout: it adds `improvedUpper` and the
# `green_25.variants.upper_exp_sqrt_log` statement to FC's own `25.lean`, plus the
# `AtlasVerified` lean_lib stanza to `lakefile.toml`. Without the patch these modules
# do not compile, and `Green25Compare`'s `rfl` checks against FC's `improvedUpper`
# have nothing to check against.
source "$(dirname "$0")/lakeenv.sh"

rm -rf "$FC/AtlasVerified"
mkdir -p "$FC/AtlasVerified"
cp -r "$REPO/AtlasVerified/." "$FC/AtlasVerified/"
echo "synced $(find "$FC/AtlasVerified" -name '*.lean' | wc -l) .lean files into the checkout"

cp "$REPO"/Green25Improved/Green25*.lean "$FC/FormalConjectures/GreensOpenProblems/"
echo "synced $(ls "$REPO"/Green25Improved/Green25*.lean | wc -l) Green25 modules into FormalConjectures/GreensOpenProblems/"

# Apply the FC patch if it has not already been applied.
cd "$FC" || exit 1
if git apply --reverse --check "$REPO/Green25Improved/formal-conjectures.patch" 2>/dev/null; then
  echo "formal-conjectures.patch: already applied"
elif git apply "$REPO/Green25Improved/formal-conjectures.patch" 2>/dev/null; then
  echo "formal-conjectures.patch: applied"
else
  echo "formal-conjectures.patch: FAILED to apply -- checkout is not in a state this patch expects" >&2
  exit 1
fi
