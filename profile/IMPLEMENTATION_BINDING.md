# S2a implementation binding and interpretation register

Authoritative specification: `S2_PREREG_v0.2.4_ACCEPTED_S2a.md` (SHA-256
`5f5a7eaf538f3051adca384f0aaf231f93c218682401fc75be1a3566c8283c82`, checked by
`scripts/verify.sh`). Normative profile: P10 Underdetermination Profile v0.1.1
(`vendor/p10-underdetermination-lean-s1/profile/normative/`, SHA-256 `b92c0d68…6558`).
Nothing below amends either document. Where the text was silent or self-contradictory, the
choice made is recorded here so that the adversarial review can overrule it.

## 1. Prereg section → module map

| Prereg | Module |
|---|---|
| §6 core objects | `P10S2/Types.lean` (+ `LogView`, `LeafFacts`, `Row`, `DetailedEntry`, `Transcript`, `CoverageOutcome`) |
| §15 transcript codec laws | `P10S2/Codec.lean` (combinators, both laws), `P10S2/TranscriptCodec.lean` (`decode_encode_transcript`, `encode_decode_transcript`) |
| §6a `ProfileArtifactS2V0` | `P10S2/ProfileArtifact.lean` (`decode_encode_profile`, `encode_decode_profile`) |
| §13 fixture, bundle | `P10S2/Fixture.lean` (`fx`, `fx_projection`, `bundle_perm/dedup/faithful/refines`, truth table) |
| §6, §7 classification, C1–C12 | `P10S2/Coverage.lean` (`coverageCheck`, `coverageCheckM`) |
| §8 | `P10S2/CoverageSpec.lean` (`coverage_sound`, `coverage_sound_view`, `TranscriptFaithful`) |
| §9, §10 | `P10S2/Composition.lean` (`s2_end_to_end`, `p10Verdict*`, `e2eCheck`, `e2eCheck_sound`) |
| §11, §12 | `vectors/`, `P10S2Tests/V_*.lean`, `P10S2TestsMustFail/` |
| §6a manifests, partition, TB7, acceptance | `manifest/`, `scripts/s2a.py`, `scripts/verify.sh` |

## 2. Premises that Lean does not discharge (prereg TB2–TB7)

`TranscriptFaithful T V` (S2b: leaves reconstruct `root(S_R)`, checkpoint signature, correct
`sub`/`iss`/`kind`/payload/`SigObservation`, availability); transparency-service non-equivocation
(TB3); checkpoint selection and freshness (TB6: nothing is claimed about leaves at
`idx ≥ size(S_R)`); the adequacy of the frozen admission/relevance/authorization policy; the
running build's identity (TB7, a harness check, not a Lean theorem).

## 3. Interpretations and decisions (for the reviewer to overrule)

**I-1 — PREREG CONFLICT: C11 vs S2-P2.** C11 requires a valid owner adjudication after the
closure, else HALT. S2-P2 lists "commitment, A1, closure [A1]" (no adjudication) and expects
`accept`; S2-P1 lists the adjudication explicitly. Both cannot hold literally. Implemented: C11
exactly as written; the P2 vector includes the adjudication leaf (like P1); the literal
no-adjudication scenario is kept as vector `P2x` and HALTs at C11. The prereg owner must decide
which text is amended. Flipping it is a one-line change in `coreCheck` plus vector `P2x`.

**I-2 — payload model.** §6 leaves `Payload` abstract. Variants: `profileCommit(digest)`,
`instanceCommit(InstanceCommitment)`, `admission(item)`, `closure(ClosurePayload)`,
`adjudication(profileRef, commitRef, closureRef)`. A payload must be of the entry's `kind`
(`kindMatches`). `ClosurePayload` has the profile §2.6 fields; `closed_evidence_set_digest` is
**carried, not checked** (binding of `e` is via C12 and §9). The adjudication carries the three
references because something must be able to *cite* a lifecycle entry for C5/M28.

**I-3 — C5.** A valid owner adjudication citing a matching-`sub` lifecycle entry whose `iss` is
not the owner → REJECT. Other reference-consistency of the adjudication is not checked.

**I-4 — admitter set.** `authorized_admitter_set_digest` stays an `iss`-set digest (TB4). The set
Lean uses is the `KeyResolutionV0` keys other than the owner, and C1 additionally requires
`commitment.authorized_admitter_set_digest = SHA-256("P10S2-AdmitterSet-v0:" ++ canonical list of
those `iss`)` (reason `c1_admitterSetDigest`). This check is not in the §7 C1 enumeration; without
it Lean could not decide authorization from the *committed* set.

**I-5 — pre-closure digest (M29).** Profile M29 fixes no byte format. Implemented:
`SHA-256("P10S2-PreclosureView-v0:" ++ list-encoding of (idx, kind, iss))` over the entries
strictly before the closure that are valid owner lifecycle entries or `RelevantAdmission`s
(earlier closure attempts count as owner lifecycle entries).

**I-6 — validity.** Closure valid iff owner `iss`, `sig = verified`, kind/payload agree,
`instance_subject` matches, `terminal = true`, digest as I-5. Commitment valid iff owner-signed
and its `(owner, request_id, subject)` tuple matches; a single valid commitment must equal the
frozen `inst`. Profile commitment valid iff owner-signed and its digest equals
`inst.profile_digest`. `RelevantAdmission` per C8 (payload must be `admission(item)`).

**I-7 — C3/C4 "before the first RelevantAdmission"** is implemented as "less than every
RelevantAdmission index" (vacuous when there is none).

**I-8 — evaluation order.** §7 fixes only C1 before C2. Implemented: C1 (contiguity, row/detail
correspondence, log identity, profile digest, strict `pB` decode, fixed fields, key-resolution
digest, admitter-set digest), C2 (rows, subject payloads, key availability), then C3…C12 in table order.

**I-9 — N7 "checkpoint material missing".** `Transcript.checkpoint` is mandatory, so absence is
not representable inside `coverageCheck`. `coverageCheckM` takes `Option Transcript`; `none` →
`halt tb5_checkpointMaterialUnavailable`.

**I-10 — N20/N21 are TB7, not Lean.** The Lean checker accepts those vectors (manifest identity
is not a Lean fact); `scripts/s2a.py tb7-vectors` produces REJECT / HALT. Both facts are tested.

**I-11 — `decide +kernel` and axioms.** Vector theorems use `decide +kernel` (kernel evaluation;
no `Lean.ofReduceBool`). The checker library's theorems use the three standard axioms
(`profile/AXIOM_POLICY.md`); S1's stricter axiom-free policy is not claimed for S2a.

**I-12 — S1 dependency.** Required at `v0.1.0-s1-ratified` as a Lake `path` dependency on a
byte-for-byte copy of the tag's tree (`vendor/`, git tree id `6cdf48c2…` = the tag's tree),
because S1 is a private repository (CI cannot clone it) and §15 requires offline reproduction.
`s1-identity` re-verifies the copy against S1's own `SHA256SUMS`, the pinned S1 manifest digest
and the git tree id. S1 is not modified.

**I-13 — codec formats** (prereg leaves them open). Transcript: binary, domain-separated,
naturals as `⌊n/255⌋` bytes `255` then `n mod 255` (so every natural is encodable and bytes are
always < 256). `pB`: flat canonical JSON in S1's style (sorted keys, tokens over `[A-Za-z0-9_.:-]`),
nested `key_resolution` object with strictly ascending keys; the three constant fields
(`artifact_version`, `leaf_encoding`, `log_identity_scheme`) are part of the literal skeleton.

**I-14 — manifest fields.** `lean_toolchain_artifact_digest` = SHA-256 of the `lean` executable
(identical to S1's pin); the conda package digest is pinned in `scripts/install_toolchain.sh`
(covered by `checker_source_tree_digest`). `dependency_lock_digest` and `build_manifest_digest`
digest canonical JSON maps of the files they name.

**I-15 — fixture.** `admissible := true` for both item forms. `AdmissionProfile` has extra fields
`inEb`/`inE_spec` (decidable `Eπ`, needed to execute C12) and `fixtureId`.

**I-16 — not checked by S2a v0 (carried fields).** `subject_derivation_digest`,
`leaf_encoding_profile_digest`, `evidence_scope_digest`, `admission_rule_digest`,
`coverage_rule_digest`, `closed_evidence_set_digest`; `SubjectDeriveV0` is not recomputed.

**I-17 — kernel replay** (`leanchecker`) covers the checker library; the vector library is
kernel-checked by `lake build` (each vector theorem is one `decide +kernel`) and audited by the
harness, but not replayed a second time.

**I-18 — additions.** Vectors `P2x`, `P3b`, variants (`N4b`, `N6b/c`, `N7a–d`, `N13a/b`, `N22a–c`,
`N23a–c`) and `X1`–`X8` exist beyond the §11 table; none weakens a preregistered vector.

## v0.2.5 hardening — interpretations and deviations (prereg `e077c30e…`)

- `PreclosureDigestV0`: kind tokens are the `Kind` constructor names (prereg leaves the kind string unspecified).
- Issuer/owner `iss` must lie in the token alphabet (`c1a_issuerNotToken`); `owner ∉ authorized_admitters` is enforced as `c1_ownerInAdmitters`. Extra vectors X9, X10.
- `profile/LeafEncodeV0_SPEC.md` is authored by the implementation (prereg gives no content). It binds the frozen profile §2.4 definition (exact registered Signed Statement bytes + format/media-type identifier → RFC 9162 leaf input) and explicitly states that the frozen profile and prereg define no byte-level mapping; S2a only binds the artifact digest, executable conformance is S2b and needs a normative decision.
- Kernel cost: each vector needs ~6 GB, so `verify.sh` builds vector modules two at a time; end-to-end vectors are split over `V_<id>`, `V_<id>_dig`, `V_<id>_e2e` (`e2eCheck_of_parts`, `runE2E_of_inst`).
- D1/D2 expected bytes come from independent Python (`scripts/s2a.py gen-differential`, frozen S1 `p10tool` JCS; raw-bytes digest for D2).
