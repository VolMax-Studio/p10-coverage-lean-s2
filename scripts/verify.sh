#!/usr/bin/env bash
# S2a acceptance command (prereg §15). Fail-closed: any failing step aborts; no network, no
# `lake update`, no `elan`. A pass is NOT a gate verdict and NOT ratification.
#
#   canonical run (pins obtained out of band):
#     P10_EXPECT_VERIFIER_MANIFEST_SHA256=<sha256> P10_EXPECT_VECTOR_MANIFEST_SHA256=<sha256> ./scripts/verify.sh
#   self-consistency run (reads profile/S2A_PINS.txt from the same tree; proves consistency only):
#     P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh
#
# Requires on PATH: the pinned lean/lake/leanchecker (scripts/install_toolchain.sh), python3 with
# requirements.lock, sha256sum.
set -euo pipefail
cd "$(dirname "$0")/.."

step() { printf '\n==> %s\n' "$*"; }
die()  { printf 'VERIFY FAIL: %s\n' "$*" >&2; exit 1; }
for t in lean lake leanchecker python3 sha256sum; do
  command -v "$t" >/dev/null 2>&1 || die "required tool missing: $t"
done

step "pins (root of trust for both manifests)"
if [[ -n "${P10_EXPECT_VERIFIER_MANIFEST_SHA256:-}" && -n "${P10_EXPECT_VECTOR_MANIFEST_SHA256:-}" ]]; then
  pin_v="$P10_EXPECT_VERIFIER_MANIFEST_SHA256"; pin_t="$P10_EXPECT_VECTOR_MANIFEST_SHA256"
  echo "  using externally supplied pins"
elif [[ "${P10_ALLOW_INTREE_PIN:-0}" == "1" ]]; then
  pin_v="$(grep '^verifier_manifest_sha256=' profile/S2A_PINS.txt | cut -d= -f2)"
  pin_t="$(grep '^vector_manifest_sha256=' profile/S2A_PINS.txt | cut -d= -f2)"
  echo "  WARNING: in-tree pins: this run proves self-consistency only; it is NOT an external trust anchor"
else
  die "external pins required (P10_EXPECT_VERIFIER_MANIFEST_SHA256 and P10_EXPECT_VECTOR_MANIFEST_SHA256), or P10_ALLOW_INTREE_PIN=1"
fi
[[ "$pin_v" =~ ^[0-9a-f]{64}$ && "$pin_t" =~ ^[0-9a-f]{64}$ ]] || die "malformed manifest pin"

step "python environment (requirements.lock)"
python3 scripts/check_env.py requirements.lock || die "python environment differs from requirements.lock"

step "toolchain identity"
lean --version
[[ "$(cat lean-toolchain)" == "leanprover/lean4:v4.33.0" ]] || die "lean-toolchain differs from the pinned identifier"
lean --version | grep -q "version 4.33.0" || die "lean is not 4.33.0"

step "accepted preregistration artifact (exact bytes)"
echo "5f5a7eaf538f3051adca384f0aaf231f93c218682401fc75be1a3566c8283c82  profile/S2_PREREG_v0.2.4_ACCEPTED_S2a.md" \
  | sha256sum --check --quiet || die "profile/S2_PREREG_v0.2.4_ACCEPTED_S2a.md differs from the accepted artifact"

step "accepted preregistration v0.2.5 (exact bytes)"
echo "e077c30edb33d4799079185ccc4bb3add7e32a5ee4318a358c77a139039c437f  profile/S2_PREREG_v0.2.5.md" \
  | sha256sum --check --quiet || die "profile/S2_PREREG_v0.2.5.md differs from the accepted artifact"

step "frozen S1 dependency (vendored tag v0.1.0-s1-ratified)"
python3 scripts/s2a.py s1-identity

step "Lean source policy"
python3 scripts/check_no_forbidden_scope.py

step "clean build of the checker library (warnings are errors), twice (idempotence)"
rm -rf .lake/build vendor/p10-underdetermination-lean-s1/.lake/build
lake build P10S2 --wfail
lake build P10S2 --wfail >/dev/null

step "kernel replay: leanchecker over every module of the checker library"
lake env leanchecker P10S2 || die "leanchecker replay failed"

step "axiom audit (every non-private theorem; permitted axioms only)"
python3 scripts/s2a.py check-audit

step "VerifierManifestS2aV0: recompute for the running build and compare"
python3 scripts/s2a.py check-verifier
[[ "$(sha256sum manifest/VerifierManifestS2aV0.json | cut -d' ' -f1)" == "$pin_v" ]] \
  || die "VerifierManifestS2aV0 digest differs from the pin"

step "manifest partition rule"
python3 scripts/s2a.py partition

step "VectorManifestS2aV0: exact file set and digests"
python3 scripts/s2a.py check-vector
[[ "$(sha256sum manifest/VectorManifestS2aV0.json | cut -d' ' -f1)" == "$pin_t" ]] \
  || die "VectorManifestS2aV0 digest differs from the pin"

step "LeafEncodeV0 spec artifact digest (independent recomputation)"
python3 scripts/s2a.py leafspec

step "vectors P1-P3, P2x, N0-N36c, D1, D2 (+ additions): kernel-checked outcomes (decide +kernel)"
# Each vector's kernel evaluation needs ~6 GB: build at most two at a time (plain `lake build`
# would run one per core and be OOM-killed on 16 GB machines), then confirm the whole library.
ls P10S2Tests/V_*.lean | sed 's#/#.#; s#\.lean$##' | sort \
  | xargs -P2 -I{} sh -c 'lake build {} --wfail >/dev/null || { echo "vector build failed: {}" >&2; exit 255; }' \
  || die "a vector module failed to build"
lake build P10S2Tests --wfail

step "end-to-end must-fail files (N0, N11, and the dropped-hypothesis controls)"
python3 scripts/s2a.py mustfail

step "TB7 harness (verifier identity; N20 REJECT, N21 HALT)"
python3 scripts/s2a.py tb7-vectors

step "result matrix"
python3 scripts/s2a.py matrix

step "artifact digests"
sha256sum manifest/VerifierManifestS2aV0.json manifest/VectorManifestS2aV0.json \
  vendor/p10-underdetermination-lean-s1/manifest/VerifierManifestS1.json

echo
echo "S2a ACCEPTANCE COMMAND PASS — implementation checks only; not a gate verdict, not ratification."
