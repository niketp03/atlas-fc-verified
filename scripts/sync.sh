#!/bin/bash
# Copy this repo's Lean sources into the formal-conjectures checkout.
source "$(dirname "$0")/lakeenv.sh"
rm -rf "$FC/AtlasVerified"
mkdir -p "$FC/AtlasVerified"
cp -r "$REPO/AtlasVerified/." "$FC/AtlasVerified/"
echo "synced $(find "$FC/AtlasVerified" -name '*.lean' | wc -l) .lean files into the checkout"
