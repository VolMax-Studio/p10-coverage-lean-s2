#!/usr/bin/env bash
# Scaffold self-check. Checks only things that exist; never prints a
# coverage/verification PASS.
set -euo pipefail
cd "$(dirname "$0")/.."

need=(README.md LICENSE lean-toolchain lakefile.toml lake-manifest.json
  S1_DEPENDENCY.md profile/S2_PREREG_v0.2_DRAFT.md profile/TRUST_BOUNDARIES.md
  profile/CLAIM_SCOPE.md profile/IMPLEMENTATION_BINDING.md P10S2.lean
  tests/README.md tests/PositiveControl.lean scripts/check_no_forbidden_scope.py)
for m in Types Checkpoint Transcript Authorization Relevance Bundle Closure \
         CoverageSpec Coverage Composition Fixtures AxiomAudit; do
  need+=("P10S2/$m.lean"); done
for f in "${need[@]}"; do [ -f "$f" ] || { echo "MISSING: $f"; exit 1; }; done
n=$(ls tests/planned/S2-N*.md | wc -l)
[ "$n" -eq 15 ] || { echo "expected 15 planned vectors, found $n"; exit 1; }
grep -q 'e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1' S1_DEPENDENCY.md \
  || { echo "S1 pin missing"; exit 1; }
grep -q 'NOT RATIFIED' profile/S2_PREREG_v0.2_DRAFT.md \
  || { echo "prereg draft must say NOT RATIFIED"; exit 1; }

python3 scripts/check_no_forbidden_scope.py

if ! command -v lake >/dev/null 2>&1; then
  echo "lake not found: Lean build NOT performed; scaffold self-check incomplete" >&2
  exit 2
fi
[ "$(cat lean-toolchain)" = "leanprover/lean4:v4.33.0" ] || { echo "toolchain drift"; exit 1; }
lake build

# Axiom audit: any theorem must have a `#print axioms` entry and only
# standard axioms.
thms=$(grep -hoE '^\s*theorem\s+[A-Za-z0-9_.]+' P10S2/*.lean | awk '{print $2}' || true)
if [ -z "$thms" ]; then
  echo "axiom audit: no theorems present (vacuous)"
else
  for t in $thms; do
    grep -q "#print axioms .*${t}" P10S2/AxiomAudit.lean \
      || { echo "theorem $t lacks axiom-audit entry"; exit 1; }
  done
  out=$(lake env lean P10S2/AxiomAudit.lean)
  echo "$out"
  echo "$out" | grep -oE '\[[^]]*\]' | tr -d '[]' | tr ',' '\n' | sed 's/ //g' \
    | grep -vxE 'propext|Classical.choice|Quot.sound|' && { echo "non-standard axiom"; exit 1; } || true
fi

echo "S2 SCAFFOLD SELF-CHECK PASS — no coverage theorem is claimed."
