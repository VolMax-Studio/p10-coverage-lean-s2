#!/usr/bin/env bash
# Maintainer-only regeneration, in dependency order (the prereg §6a hash-cycle rule):
#   checker sources -> checker .olean -> VerifierManifestS2aV0 -> pB/vectors -> VectorManifestS2aV0.
# Not part of the acceptance command.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/s2a.py gen-audit                       # covered source: must precede the build
rm -rf .lake/build vendor/p10-underdetermination-lean-s1/.lake/build
lake build P10S2 --wfail
md="$(python3 scripts/s2a.py gen-verifier)"            # digest of the manifest of THIS build
echo "verifier manifest digest: $md"
lake build P10S2Tests.Catalogue --wfail
lake env lean --run P10S2Tests/Gen.lean "$md"          # writes vectors/ and P10S2Tests/V_*.lean
rm -f .lake/build/lib/lean/P10S2Tests/V_*.olean .lake/build/lib/lean/P10S2Tests/V_*.ilean
python3 scripts/s2a.py gen-differential
python3 scripts/gen_d2_small.py                        # D2 small differential bytes (independent hashlib)
vd="$(python3 scripts/s2a.py gen-vector)"
printf 'verifier_manifest_sha256=%s\nvector_manifest_sha256=%s\n' "$md" "$vd" > profile/S2A_PINS.txt
echo "vector manifest digest: $vd"
