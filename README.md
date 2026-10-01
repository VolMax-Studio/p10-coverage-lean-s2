# p10-coverage-lean-s2 — P10 S2a (coverage / evidence-closure kernel)

**Status: implementation of S2a under preregistration v0.2.6 (amending v0.2.5 and the accepted
v0.2.4). Implementation checks and independent hosted CI only: this is not human ratification, and
nothing here has been merged or tagged. S2b and S3 are not authorized and not present.**

S2a proves coverage properties **conditionally over a checkpoint-bound authenticated
transcript**. Cryptographic authentication and production full-prefix replay belong to S2b and are
outside this repository.

S2 completeness is **relative to the committed policy/scope and the prefix through `S_R`**; it is
**not** a claim that all relevant evidence existing in the world was registered.

## What is implemented

| Area | Where | Main results |
|---|---|---|
| Core data, `CoverageOutcome` (`accept e` / `reject` / `halt`, `halt` carries no evidence) | `P10S2/Types.lean` | |
| Strict canonical codecs | `P10S2/Codec.lean`, `TranscriptCodec.lean`, `ProfileArtifact.lean` | `decode_encode_transcript`, `encode_decode_transcript`, `decode_encode_profile`, `encode_decode_profile` (general laws, not per-vector) |
| Fixture `fx` over the frozen `P10.S1.profile`, total `bundle` | `P10S2/Fixture.lean` | `fx_projection` (`rfl`), `bundle_perm`, `bundle_dedup`, `bundle_faithful`, `bundle_refines`, truth table |
| JCS digests of prereg §6b (`ClaimDigestV0`, `EvidenceDigestV0`, admitters, key resolution, pre-closure view, descriptors, `LeafEncodeSpecArtifactDigestV0`) | `P10S2/Digests.lean` | |
| Lean-side authorization / relevance / lifecycle, `coverageCheck` C1, C1a–C1c, C2–C13 | `P10S2/Coverage.lean` | |
| Specification and soundness | `P10S2/CoverageSpec.lean` | `coverage_sound`, `coverage_sound_view` (under `TranscriptFaithful`) |
| Byte-level S2 → S1 composition, HALT/REJECT ⇒ no verdict | `P10S2/Composition.lean` | `s2_end_to_end`, `e2eCheck_sound`, `p10Verdict_*`, `*_no_verdict` |
| Vectors P1–P3, P2x, N0–N36c, D1, D2, K1–K8 (+ additions), must-fail files | `vectors/`, `P10S2Tests/`, `P10S2TestsMustFail/` | every vector is one kernel-checked theorem (`decide +kernel`) |
| Manifests, partition check, TB7 harness | `manifest/`, `scripts/s2a.py`, `scripts/verify.sh` | |

The exact theorem statements, premises, limitations and every interpretation of unspecified or
contradictory prereg text are in `profile/IMPLEMENTATION_BINDING.md` (entries marked SUPERSEDED or
RESOLVED describe v0.2.4-era behaviour replaced by v0.2.5/v0.2.6). `profile/LeafEncodeV0_SPEC.md` is
the committed `LeafEncodeV0` specification (wrapper over the exact submitted statement bytes);
S2a binds its digest and does not execute it (S2b).

## Reproduce

```sh
eval "$(scripts/install_toolchain.sh)"     # pinned conda-forge Lean 4.33.0 (no elan, no lake update)
P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh # self-consistency run; canonical runs pass pins out of band
```

Each vector needs about 6 GB of kernel memory, so vector modules are built one at a time by default
(about an hour in total); `P10_VECTOR_JOBS=2` is an explicit option on machines with 16 GB.

No network and no cryptographic library is needed to reproduce the Lean result (SHA-256 is frozen
S1's kernel-evaluable implementation). A pass prints
`S2a ACCEPTANCE COMMAND PASS — implementation checks only; not a gate verdict, not ratification.`

## Dependencies

S1 is required at the frozen ratified tag `v0.1.0-s1-ratified` (`S1_DEPENDENCY.md`), realised as a
verified byte-for-byte vendored copy of the tag's tree and a Lake `path` dependency.

## Premises not discharged in Lean

`TranscriptFaithful(T, V)` (S2b), transparency-service non-equivocation, checkpoint selection and
freshness (TB6), adequacy of the frozen policy/scope, and the running build's identity (TB7, checked
by the harness). See `profile/TRUST_BOUNDARIES.md` and `profile/CLAIM_SCOPE.md`.
