#!/bin/bash
# Shared environment for building this library inside the formal-conjectures checkout.
#
# Why build there rather than as a standalone lake package: this repo's proofs need
# Mathlib and FormalConjectures, both of which are already built in that checkout
# (~7.2 GB of oleans). A standalone package would re-clone Mathlib and rebuild
# everything. So `sync.sh` copies AtlasVerified/ into the checkout and we build in
# place. A symlink does NOT work -- lake hangs indefinitely on a symlinked directory
# in the package root -- so this is a real copy.
export HOME=/scratch/nnp5656
export PATH=/scratch/nnp5656/.elan/bin:$PATH
export MATHLIB_CACHE_FROM=master
export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
export SSL_CERT_FILE=/etc/pki/tls/certs/ca-bundle.crt
export FC=/scratch/nnp5656/projects/fc/formal-conjectures
export REPO=/scratch/nnp5656/projects/atlas-fc-verified
