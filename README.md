# p10-coverage-lean-s2 — P10 S2a (coverage kernel) — SCAFFOLD

**Status: DRAFT scaffold. Not ratified. No coverage theorem is implemented or claimed.**

S2a proves coverage properties **conditionally over a checkpoint-bound
authenticated transcript**. Cryptographic authentication and production
full-prefix replay belong to S2b (`p10-replay-verifier`) and are outside this
repository.

S2 completeness is **relative to the committed policy/scope and the prefix
through `S_R`**; it is **not** a claim that all relevant evidence existing in
the world was registered.

## What this repository is

The pure/offline Lean coverage kernel. It contains no COSE/CWT, signature
verification, key fetching, SCRAPI, network code, production Merkle/VDS replay
or SCITT Receipt code. Those belong to S2b / S3.

## Current contents

Types, outcome type (`accept Evidence | reject | halt`; `halt` carries no
evidence), checkpoint/transcript/closure data structures, toy fixture data
types, and module boundaries for Authorization, Relevance, Bundle,
CoverageSpec, Coverage and Composition (placeholders only). See
`profile/` for the draft prereg delta register, trust boundaries, claim scope
and S2a/S2b binding, and `tests/planned/` for negative-vector specifications.

## Not yet present (deliberately)

`coverageCheck`, `CoverageSpec`, `coverage_sound`,
`coverage_then_underdetermined`, the composed verdict function, any passing
fixture. See `P10S2/Coverage.lean`.

## S1 dependency

S2 depends on the frozen, human-ratified S1 release tag
`v0.1.0-s1-ratified` (peeled commit `e4db3747…`); see `S1_DEPENDENCY.md`
(single location). S1 is ratified; S2 is not.

## Verification

CI (`.github/workflows/verify.yml`) runs the same checks on the pinned
conda-forge Lean 4.33.0 toolchain (no elan). `scripts/verify.sh` checks structure, forbidden constructs/scope, the Lean
build and (vacuously, for now) the axiom audit. A pass means only:
`S2 SCAFFOLD SELF-CHECK PASS — no coverage theorem is claimed.`
