#!/bin/bash
# Installs landrun, lean4export, comparator and nanoda at the commits pinned by
# lean-eval SECURITY.md. Paths below are specific to the NYU torch cluster.
# Install the four external tools lean-eval's `lake test` shells out to,
# each at the commit pinned in lean-eval's SECURITY.md / README.
set -x
export HOME=/scratch/nnp5656
export RUSTUP_HOME=/scratch/nnp5656/.rustup
export CARGO_HOME=/scratch/nnp5656/.cargo
export GOPATH=/scratch/nnp5656/go
export GOCACHE=/scratch/nnp5656/.cache/go-build
export PATH=/scratch/nnp5656/.elan/bin:/share/apps/go/1.25.1/bin:$CARGO_HOME/bin:$GOPATH/bin:$PATH
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export SSL_CERT_FILE=/etc/pki/tls/certs/ca-bundle.crt
TOOLS=/scratch/nnp5656/lean-eval-tools
LE=$TOOLS/lean-eval
mkdir -p $TOOLS && cd $TOOLS || exit 1

# lean-eval itself (the real checkout we will work in)
if [ ! -d $LE/.git ]; then git clone https://github.com/leanprover/lean-eval.git $LE || exit 1; fi

echo "===== 1/4 landrun (go) ====="
go install github.com/zouuup/landrun/cmd/landrun@5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
echo "LANDRUN_EXIT=$?"; command -v landrun

echo "===== 2/4 lean4export ====="
[ -d lean4export ] || git clone https://github.com/leanprover/lean4export.git
( cd lean4export && git checkout -q 4e7915201d3f9f04470d9eae002fa695f7cdc589 \
  && cp $LE/lean-toolchain lean-toolchain && lake build lean4export )
echo "LEAN4EXPORT_EXIT=$?"

echo "===== 3/4 comparator ====="
[ -d comparator ] || git clone https://github.com/leanprover/comparator.git
( cd comparator && git checkout -q 71b52ec29e06d4b7d882726553b1ceb99a2499e0 && lake build comparator )
echo "COMPARATOR_EXIT=$?"

echo "===== 4/4 nanoda ====="
[ -d nanoda_lib ] || git clone https://github.com/robsimmons/nanoda_lib.git
( cd nanoda_lib && git checkout -q 68d5ca9db226849b41a6fff59d796ff19d0a8840 && cargo build --release )
echo "NANODA_EXIT=$?"

echo "===== results ====="
ls -la $GOPATH/bin/landrun $TOOLS/lean4export/.lake/build/bin/lean4export \
       $TOOLS/comparator/.lake/build/bin/comparator $TOOLS/nanoda_lib/target/release/nanoda_bin 2>&1
