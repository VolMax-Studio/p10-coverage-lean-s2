# S2a implementation binding and interpretation register

Authoritative specification (current): `S2_PREREG_v0.2.6.md` (SHA-256
`d6fbeb13bf229d0e10c17031a887ef7944ae8e6acc68b6e898a007d5a851c9e0`), which amends
`S2_PREREG_v0.2.5.md` (`e077c30edb33d4799079185ccc4bb3add7e32a5ee4318a358c77a139039c437f`), which
amends `S2_PREREG_v0.2.4_ACCEPTED_S2a.md` (`5f5a7eaf538f3051adca384f0aaf231f93c218682401fc75be1a3566c8283c82`).
All three digests are checked by `scripts/verify.sh`. Normative profile: P10 Underdetermination
Profile v0.1.1 (`vendor/p10-underdetermination-lean-s1/profile/normative/`, SHA-256 `b92c0d68…6558`);
no profile amendment is required. Nothing below amends any of these documents.

**How to read this register.** Sections I-1 … I-18 record the v0.2.4-era interpretations as they were
made, for the audit trail. Entries marked **SUPERSEDED** or **RESOLVED** describe behaviour that
prereg v0.2.5/v0.2.6 replaced; the final section ("v0.2.5/v0.2.6 hardening") and the code are
authoritative. The current behaviour, in short: C1a–C1c check owner = issuer, subject derivation and
the five commitment descriptors; the admitter set is the explicit `pB.authorized_admitters`
(never derived from `KeyResolutionV0`, which is key availability only); C3 requires exactly one
owner profile commitment with the committed digest; C11 requires every adjudication after the
closure to cite exactly the selected profile, commitment and closure; C13 checks
`closed_evidence_set_digest = EvidenceDigestV0`; all structured digests are JCS (§6b), with the
kind tokens of the v0.2.6 table.

## 1. Prereg section → module map

| Prereg | Module |
|---|---|
| §6 core objects | `P10S2/Types.lean` (+ `LogView`, `LeafFacts`, `Row`, `DetailedEntry`, `Transcript`, `CoverageOutcome`) |
| §15 transcript codec laws | `P10S2/Codec.lean` (combinators, both laws), `P10S2/TranscriptCodec.lean` (`decode_encode_transcript`, `encode_decode_transcript`) |
| §6a `ProfileArtifactS2V0` | `P10S2/ProfileArtifact.lean` (`decode_encode_profile`, `encode_decode_profile`) |
| §13 fixture, bundle | `P10S2/Fixture.lean` (`fx`, `fx_projection`, `bundle_perm/dedup/faithful/refines`, truth table) |
| §6, §7 classification, C1, C1a–C1c, C2–C13 | `P10S2/Coverage.lean` (`coverageCheck`, `coverageCheckM`) |
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

> **RESOLVED by prereg v0.2.5 (I-1):** S2-P2 and S2-P3 now include the owner adjudication; `P2x` (no adjudication) is the preregistered HALT (C11) vector.

**I-1 — PREREG CONFLICT: C11 vs S2-P2.** C11 requires a valid owner adjudication after the
closure, else HALT. S2-P2 lists "commitment, A1, closure [A1]" (no adjudication) and expects
`accept`; S2-P1 lists the adjudication explicitly. Both cannot hold literally. Implemented: C11
exactly as written; the P2 vector includes the adjudication leaf (like P1); the literal
no-adjudication scenario is kept as vector `P2x` and HALTs at C11. The prereg owner must decide
which text is amended. Flipping it is a one-line change in `coreCheck` plus vector `P2x`.

> **SUPERSEDED in part:** `closed_evidence_set_digest` is now checked (C13, prereg B1) and the adjudication's three references are checked against the selected profile/commitment/closure (C11, prereg B5). The payload variants themselves are unchanged.

**I-2 — payload model.** §6 leaves `Payload` abstract. Variants: `profileCommit(digest)`,
`instanceCommit(InstanceCommitment)`, `admission(item)`, `closure(ClosurePayload)`,
`adjudication(profileRef, commitRef, closureRef)`. A payload must be of the entry's `kind`
(`kindMatches`). `ClosurePayload` has the profile §2.6 fields; `closed_evidence_set_digest` is
**carried, not checked** (binding of `e` is via C12 and §9). The adjudication carries the three
references because something must be able to *cite* a lifecycle entry for C5/M28.

**I-3 — C5.** A valid owner adjudication citing a matching-`sub` lifecycle entry whose `iss` is
not the owner → REJECT. (Reference consistency of the adjudication is now checked by C11, prereg v0.2.5 B5: every adjudication after the closure must cite exactly the selected profile, commitment and closure, else REJECT.)

> **SUPERSEDED by prereg v0.2.5 (B3):** the authorized set is the explicit `pB.authorized_admitters`; `KeyResolutionV0` grants no authorization (an authorized issuer without a key yields `keyUnavailable` → HALT, a key without authorization is not authorized). The digest is `AuthorizedAdmittersDigestV0` (JCS), reason `c1b_admittersDigest`.

**I-4 — admitter set.** `authorized_admitter_set_digest` stays an `iss`-set digest (TB4). The set
Lean uses is the `KeyResolutionV0` keys other than the owner, and C1 additionally requires
`commitment.authorized_admitter_set_digest = SHA-256("P10S2-AdmitterSet-v0:" ++ canonical list of
those `iss`)` (reason `c1_admitterSetDigest`). This check is not in the §7 C1 enumeration; without
it Lean could not decide authorization from the *committed* set.

> **SUPERSEDED by prereg v0.2.5 (I-2) and v0.2.6 (K-1):** `PreclosureDigestV0` is a JCS digest of `{"preclosure_view": [[idx, kind, iss], …]}` with the normative kind tokens; the binary form above is kept only as the legacy form that vectors N34/N35 must reject.

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

> **UPDATED:** C1 now also contains C1a (owner = issuer, issuer token, subject derivation), C1b (owner not an admitter, admitters digest, JCS key-resolution digest) and C1c (five descriptor digests) before C2; C3 and C11 are as described at the top of this file.

**I-8 — evaluation order.** §7 fixes only C1 before C2. Implemented: C1 (contiguity, row/detail
correspondence, log identity, profile digest, strict `pB` decode, fixed fields, key-resolution
digest, admitter-set digest), C2 (rows, subject payloads, key availability), then C3…C13 in table order.

**I-9 — N7 "checkpoint material missing".** `Transcript.checkpoint` is mandatory, so absence is
not representable inside `coverageCheck`. `coverageCheckM` takes `Option Transcript`; `none` →
`halt tb5_checkpointMaterialUnavailable`.

**I-10 — N20/N21 are TB7, not Lean.** The Lean checker accepts those vectors (manifest identity
is not a Lean fact); `scripts/s2a.py tb7-vectors` produces REJECT / HALT. Both facts are tested.

**I-11 — `decide +kernel` and axioms.** Vector theorems use `decide +kernel` (kernel evaluation;
no `Lean.ofReduceBool`). The checker library's theorems use the three standard axioms
(`profile/AXIOM_POLICY.md`); S1's stricter axiom-free policy is not claimed for S2a.

**I-12 — S1 dependency.** Required at `v0.1.0-s1-ratified` as a Lake `path` dependency on a
byte-for-byte copy of the tag's tree (`vendor/`, git tree id `6cdf48c2…` = the tag's tree).
S1 is public; the vendored copy is retained because §15 requires offline reproduction and exact
binding to the ratified S1 tree rather than mutable repository state.
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

> **WITHDRAWN by prereg v0.2.5:** the descriptor digests are now checked in C1c.

**I-16 — not checked by S2a v0 (carried fields).** `subject_derivation_digest`,
`leaf_encoding_profile_digest`, `evidence_scope_digest`, `admission_rule_digest`,
`coverage_rule_digest`, `closed_evidence_set_digest`; `SubjectDeriveV0` is not recomputed.

**I-17 — kernel replay** (`leanchecker`) covers the checker library; the vector library is
kernel-checked by `lake build` (each vector theorem is one `decide +kernel`) and audited by the
harness, but not replayed a second time.

**I-18 — additions.** Vectors `P2x`, `P3b`, variants (`N4b`, `N6b/c`, `N7a–d`, `N13a/b`, `N22a–c`,
`N23a–c`) and `X1`–`X8` exist beyond the §11 table; none weakens a preregistered vector.

## v0.2.5 hardening — interpretations and deviations (prereg `e077c30e…`)

- `PreclosureDigestV0` kind tokens: superseded by prereg v0.2.6 (K-1): the hashed tokens are `profile_commit`, `instance_commit`, `admission`, `closure`, `adjudication` (`kindTok`), checked by differential vectors K1–K8 against independent Python JCS.
- Issuer/owner `iss` must lie in the token alphabet (`c1a_issuerNotToken`); `owner ∉ authorized_admitters` is enforced as `c1_ownerInAdmitters`. Extra vectors X9, X10.
- `profile/LeafEncodeV0_SPEC.md` is `LeafEncodeV0` spec v1 (wrapper mapping over the exact submitted COSE_Sign1 statement bytes and the single format id `application/scitt-statement+cose`; RFC 9162 leaf hash `SHA-256(0x00 || leaf_input)`), selected by the project owner and passed the text/spec gate (G7). It replaces the v0.2.5 placeholder (artifact digest `b9a8602f…`). S2a only binds its digest (`pB.leaf_encoding_spec_digest`); `scripts/s2a.py leafspec` recomputes the digest and the L1–L5 leaf hashes printed in the spec. Executing the mapping is S2b's obligation (L1–L8 are normative examples for S2b).
- Kernel cost: each vector needs ~6 GB, so `verify.sh` builds vector modules one at a time by default (`P10_VECTOR_JOBS=1`, fits a standard private 2 vCPU / 8 GB runner; `P10_VECTOR_JOBS=2` is an explicit operator option on 16 GB machines); end-to-end vectors are split over `V_<id>`, `V_<id>_dig`, `V_<id>_e2e` (`e2eCheck_of_parts`, `runE2E_of_inst`).
- Differential vectors: D1 and K1–K7 expected bytes come from independent Python (`scripts/s2a.py gen-differential`, frozen S1 `p10tool` JCS; K values are also checked against the prereg v0.2.6 table). D2 has three parts: a kernel `rfl` of the gated formula, two small kernel differentials against hashlib (`scripts/gen_d2_small.py`, `empty_digest.bin`, `small_digest.bin`), and the digest of the real spec file, which is checked by `scripts/s2a.py leafspec` (independent Python; `vectors/D2/spec_digest.bin`) rather than by the kernel, because kernel evaluation of the 5.7 KB file made acceptance too heavy for a standard runner.
