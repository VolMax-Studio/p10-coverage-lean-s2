# P10 S2 — Coverage / Evidence-Closure Preregistration v0.2.6

**Status:** AMENDMENT CANDIDATE to v0.2.5. Not yet gated. Authorized scope unchanged: **S2a only**. **S2b and S3 are not authorized.** Human ratification: **NOT YET**.
**Date:** 2026-09-30
**Amends:** S2 prereg v0.2.5 (SHA-256 `e077c30edb33d4799079185ccc4bb3add7e32a5ee4318a358c77a139039c437f`). Tags of the form **[A6: …]** mark statements added or changed by this amendment; **[A: …]** tags are from v0.2.5.
**Evidence reviewed:** implementation PR #3 @ `341c7df11f3b0a440083a2628d6d3b037bd98f4f` (CI run `36705606717` PASS) and its gate findings B1–B6, I-1. Code was read, not modified.
**Depends on S1:** tag `v0.1.0-s1-ratified` → `e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1`
**S2 repository state at drafting:** `p10-coverage-lean-s2` main @ `b01cf1708894ca8b0e8ab527ac61befe96012538`; draft PR #3 @ `341c7df1…` not merged.
**Normative source:** P10 Underdetermination Profile v0.1.1 (file SHA-256 `b92c0d68…6558`). This prereg does not amend the profile. Where this text and the profile disagree, the profile wins.

**Marking convention.** Every normative statement added or changed by v0.2.6 carries a tag of the form **[A6: K-1]** (finding or decision of this amendment). Tags of the form **[A: B1]** or **[A: I-2]** were introduced by v0.2.5 and are retained as written. Untagged text is unchanged from v0.2.5, except that v0.2.5 itself left text from v0.2.4 untagged.

---

## 0. Change log

### v0.1 → v0.2 (gate G1, BLOCKED, text-only)

| Item | Resolution in v0.2 (carried forward) |
|---|---|
| G1-B1 composition did not use coverage | §9 byte-level composition; S2-N0 must-fail |
| G1-B2 truncation / unnamed completeness premise | §6 checkpoint + per-leaf rows; §4 TB2 |
| G1-B3 authorization inside TCB | §6 typed status; Lean decides authorization |
| G1-F zero/many closures, M29, M5, M28, bundle totality, §1 alignment, HALT type-level, differential S2b | §7, §10, §11, §13, §15 |

### v0.2 → v0.2.1 (gate G2, security-oriented review, BLOCKED: 5 blockers, 3 fixes; plus G2-review notes)

| Item | v0.2 problem | v0.2.1 resolution |
|---|---|---|
| G2-B1 TB4 | v0.2 redefined `authorized_admitter_set_digest` to include key fingerprints. Profile v0.1.1 §2.3 states it binds "the exact frozen set of permitted CWT `iss` values". That was a normative change, not an interpretation. | §4 TB4: the digest stays an `iss` set. Key material lives in a separate `KeyResolutionV0` object that the concrete profile π binds under "lifecycle/admitter authorization" (profile §1(1), §2.2 frozen list), and therefore under `profile_digest`. |
| G2-B2 | `TranscriptFaithful` absent from §9 | §9 carries `hFaithful` over an abstract log view; `CoverageSpec` is stated over the log view, not only over `T` |
| G2-B3 | `SummaryRow.subDigest` added a collision premise | §6 rows carry canonical `sub` bytes; Lean compares bytes |
| G2-B4 | `keyUnresolved` had three meanings | §6: `iss ∉ set` → unauthorized (Lean); authorized `iss`, key material unavailable → HALT; signature fails → `badSignature` |
| G2-B5 | Bundle could be lossy despite correct refs | §13: exact characterization `bundle_faithful` against a frozen per-item relation. G2's proposed monotonicity law is kept, but it is insufficient alone (see §13). |
| G2-F TB6 | Checkpoint selection / freshness unstated | §4 TB6 |
| G2-F hP | §9 did not bind profile identity | §9 `hP` (superseded in v0.2.2 by G3-B3: profile identity is a conclusion of `hCov`, not extracted from `iB`) |
| G2-F rows | Missing row conflated attack and unavailability | §6 `RowStatus`; S2-N11 vs S2-N16 |
| G2 list item 9 | Transcript codec obligations | §15: `decode ∘ encode = id` and canonical uniqueness for transcript bytes |

### v0.2.1 → v0.2.2 (gate G3, text gate over §4/§6/§9/§13 checked against the S2 scaffold and frozen S1 code; BLOCKED: 4 blockers, 2 small fixes)

| Item | v0.2.1 problem | v0.2.2 resolution |
|---|---|---|
| G3-B1 | `sigOk` required for every matching-`sub` leaf, but `KeyResolutionV0` assigns no key to an unauthorized `iss`; S2b could neither truthfully report it nor pre-filter it without deciding authorization | §4 TB2, §6: S2b reports a pure `SigObservation` (`verified` / `badSignature` / `keyUnavailable`). Lean combines it with the committed `iss` set and owner identity. |
| G3-B2 | C2 said "no **needed** row unavailable", contradicting TB5; an unavailable leaf can hide that it belongs to the subject | §6, §7 C2, §11 S2-N16: any unavailable row in `[0, size(S_R))` → HALT. Payload availability matters only for subject entries. |
| G3-B3 | `profileBindingOf iB` cannot exist: S1 `Wire.Instance` holds only `claim, evidence, w0, w1`; the decoder checks `kind/profile/spec` against constants and discards them; the S1 verifier-manifest digest is not in `iB` at all | §9 redesigned into three links: S1 bytes (`Bound`, `decode`), concrete-profile commitment (checked inside `coverageCheck`, C1), and semantic projection (`fx.toProfile = P10.S1.profile`, by definition). The verifier-manifest digest is bound in the concrete profile artifact (§6a), not extracted from `iB`. |
| G3-B4 | Canonical uniqueness required only per vector | §15: general `encode_decode` for the transcript codec |
| G3-F1 | `bundle_refines` lacked `π.inW w`, so it did not follow from `bundle_faithful` | §13 corrected |
| G3-F2 | Scaffold `InstanceCommitment` is a placeholder without normative fields | §15 implementation note: scaffold structures MAY be changed to match profile §2.3; no placeholder API is preserved |

### v0.2.2 → v0.2.3 (gate G4, focused delta gate; G3 items PASS; 1 new blocker; plus integration finding)

| Item | v0.2.2 problem | v0.2.3 resolution |
|---|---|---|
| G4-B1 | The S2a verifier manifest was not a field of the profile artifact, so `profile_digest` did not bind the checker (profile v0.1.1 requires `profile_digest` to bind `verifier_manifest_ref` and `verifier_manifest_digest`) | §6a: exact canonical schema `ProfileArtifactS2V0` with `verifier_manifest_ref` and `verifier_manifest_digest` of `VerifierManifestS2aV0`; the S1 tag, commit, and S1 manifest digest become a frozen dependency *inside* `VerifierManifestS2aV0` |
| G4-F | "contains at least" | §6a: exact field list; unknown or missing fields → decode failure |
| G4-F | Manifest-digest mutation and unavailability untested | §11 S2-N20 (REJECT), S2-N21 (HALT, profile M33) |
| I-1 (integration finding) | **Hash cycle.** v0.2.2 embedded `profileArtifactBytes` in S2a via `filebytes%` and defined `profileDigestConst` in Lean source. Once the artifact carries the S2a manifest digest (G4-B1), and the manifest digests the S2a sources and `.olean` set (as S1's manifest does), the artifact depends on its own hash. No such byte string can exist. | §6a: the profile artifact is an **input** to the checker, like the transcript, not embedded. A manifest partition rule forbids any manifest-covered module from depending on bytes that contain a manifest digest. Manifest identity is checked by the acceptance harness (new TB7), as in S1 (profile lines on `R.verifier_digest`, M35). `profileDigestConst` is removed. |

### v0.2.3 → v0.2.4 (gate G5, focused gate over §6a/TB7/N20–N23; no semantic blocker; 2 text closures)

| Item | v0.2.3 gap | v0.2.4 resolution |
|---|---|---|
| G5-1 | `VerifierManifestS2aV0` "follows the structure of" S1's manifest; not an exact schema | §6a: exact mandatory schema using the normative `VerifierManifestV0` field names (profile v0.1.1) plus `frozen_dependencies` |
| G5-final | TB7 harness bytes not bound (`acceptance_command_digest` binds the command, not the script); "first nine fields normative" miscounted; optional file-listing contradicted the exact schema | §6a patched in place: harness sources in `checker_source_files`; eight normative fields named; path lists mandatory |
| G5-2 | Vectors and test modules were "bound by vector digests" without saying by what, and a vector manifest fed back into `pB` or the verifier manifest would reopen the cycle | §6a: separate `VectorManifestS2aV0` root; its digest MUST NOT enter `pB` or `VerifierManifestS2aV0`; the acceptance command checks file-set equality and hashes; the human ratification tag freezes both roots together |

### v0.2.4 → v0.2.5 (amendment after implementation review of PR #3 @ `341c7df`)

The implementation passed CI, the kernel checks, the axiom audit, the manifests, and TB7. The review of that implementation against this text found binding gaps that CI cannot detect. Five of them are cases where the prereg never required a named field to be checked. One is a defect in the prereg itself (B6).

| Item | Evidence in PR #3 | Resolution in v0.2.5 | Profile v0.1.1 amendment needed? |
|---|---|---|---|
| B1 | `ClosurePayload.closedEvidenceSetDigest` carried; `closureAt` does not check it; test model uses a placeholder string | §6b `EvidenceDigestV0`; §7 C13 | No. §2.6 requires the closure to bind `closed_evidence_set_digest`; §4 defines `evidence_digest` "over the JCS form of the closed set"; §2.7 requires JCS. |
| B2 | `issuerId`, `instanceOwnerIss`, `requestId`, `instanceSubject` carried; neither equality is checked; `SubjectDeriveV0` not recomputed | §6b `SubjectDeriveV0`; §7 C1 | No. §2.3 requires both equalities and delegates the frozen definition of `SubjectDeriveV0` to the profile instance. |
| B3 | `admittersOf owner keyResolution` derives the authorized set from the key map; set digest uses a custom binary codec | §4 TB4, §6a field `authorized_admitters`, §6b digest | No. This restores v0.2.4 TB4 and applies §2.7. |
| B4 | `subject_derivation_digest`, `leaf_encoding_profile_digest`, `evidence_scope_digest`, `admission_rule_digest`, `coverage_rule_digest` are carried and never checked (implementation note I-16) | §6b descriptors; §7 C1 | No. §2.3 lists the fields; their content is delegated to the profile instance. §2.7 forbids a bare identifier as a binding, so descriptors include the verifier-manifest digest (§6b). |
| B5 | C11 accepts any valid owner adjudication after the closure; `profileRef/commitRef/closureRef` unchecked | §7 C11 | No. §4 lists these refs as issuer-signed fields identifying the instance's objects. |
| B6 | `claimDigest c = SHA-256(claimTok c)`, exactly as v0.2.4 §6a required; frozen S1 tooling uses `SHA-256(JCS({"claim": tok}))` | §6b `ClaimDigestV0`; §9 | No. The v0.2.4 text contradicted §2.7. This is a prereg defect. |
| I-1 | C11 vs P2/P3: implementation kept C11, added adjudication to P2/P3, kept `P2x` | §11 P2, P3, P2x | No. |
| **I-2** (found in this review) | `checkpoint_preclosure_transcript_digest` uses a custom binary codec (implementation note I-5) | §6b `PreclosureDigestV0` | No. It is a structured field of `EvidenceClosure`; §2.7 applies. |
| **I-3** (found in this review) | `keyResolutionDigest` uses a custom binary codec | §6b | No. The digest is S2-internal, but `pB.key_resolution` is already canonical JSON, so a JCS digest costs nothing and removes a second canonical form. |

**G6 delta (applied in place to v0.2.5 before freezing).** Gate G6 passed B1–B6, I-2, I-3 and the no-amendment determination, and required:

| Item | Problem | Resolution |
|---|---|---|
| G6-B1 | C3 required only *a* valid owner profile commitment; a second owner profile commitment (same or different digest) was not rejected, contrary to profile §1(2) ("exactly one profile … bound") and M19 | §7 C3 **[A: G6-B1]**; §11 S2-N36a/b/c |
| G6-B2 | TB4 said `KeyResolutionV0` maps the owner and *every* authorized admitter, contradicting S2-N31 (authorized `iss` absent from the map → HALT) | §4 TB4 bullet 2 **[A: G6-B2]**: map membership is key availability only; N31 kept |
| G6-B3 | `leaf_encoding_spec_digest` over raw file bytes only; profile §2.7 requires binary artifacts to be digested together with a frozen format/media-type identifier | §6b `LeafEncodeSpecArtifactDigestV0` **[A: G6-B3]** |
| G6-F | §6a vector-manifest scope said N0–N23; §8 said C1–C12; §15 said "two fields added" | corrected in place |
| G6-B3 (delta) | first fix still wrapped `SHA-256(f)` in a JCS descriptor; §2.7 hashes format identifier and raw bytes directly | §6b: direct SHA-256 over fixed prefixes ++ raw bytes; §6b intro states the exception |
| G6-F (delta) | N36c missing from vector-manifest scope, §15 range, and G6-B1 row | corrected in place |

**Profile-amendment determination: none required, so no HALT.** Each fix above either checks a field that profile v0.1.1 already names, or defines the byte form of an object the profile delegates to the concrete profile instance, using the §2.7 JCS rule. Two definitions are interpretations and are recorded as such: `closed_evidence_set_digest := EvidenceDigestV0(Bundle(refs))` (B1), and the descriptor contents (B4). If the gate reads either as changing the meaning of a profile field, stop condition 10 applies.

**What survives unchanged:** transcript and profile-artifact codecs and their general laws; `fx` projection; the bundle theorem family; `coverage_sound` and `coverage_sound_view` (their specs gain conjuncts, see §8); the `TranscriptFaithful` boundary; the byte-level `s2_end_to_end` and checker-owned `e2eCheck`; the HALT/REJECT no-verdict theorems; the manifest split, partition rule, and TB7; the vector infrastructure.

### v0.2.5 → v0.2.6

| Item | Problem | Resolution |
|---|---|---|
| K-1 | §6b `PreclosureDigestV0` listed `[idx, kind, iss]` but fixed no string for `kind`; the implementation (HEAD `fbcfefa`) used Lean constructor names | §6b kind-token table **[A6: K-1]**; vectors S2-K1…K7 |
| L-1 | The committed `LeafEncodeV0` spec file (artifact digest `b9a8602f…` at `fbcfefa`) states that it defines no concrete byte mapping, so `pB` binds a placeholder | §6b rule **[A6: L-1]**: a placeholder spec is not admissible for S2a ratification. The full mapping is a separate frozen artifact, `LeafEncodeV0_SPEC` v1, not part of this prereg text. |
| D-S3 | Decision by Ivan, recorded: S3 must use a Transparency Service whose VDS is `RFC9162_SHA256` (alg 1), as profile v0.1.1 requires for `FullPrefixReplay` | §3 note **[A6: D-S3]** |

No change requires amending profile v0.1.1. The kind tokens fill the §2.7 byte form of a structured digest. `LeafEncodeV0` is a mapping that profile §2.4 delegates to the profile instance ("frozen mapping from the exact registered Signed Statement bytes and their format/media-type identifier to RFC9162 leaf input").

Integration note (not a gate item): frozen S1's `VerifierManifestS1.json` uses its own key names (e.g. `semantics_source_digest`, `olean_digest_set`) rather than the eight normative `VerifierManifestV0` names. S1 is ratified and is not changed. S2 uses the normative names exactly, so the S1 manifest is referenced only by digest.

Verified by this integration against frozen S1 at `e4db3747`: `P10.Wire.Instance` has exactly the four fields above; S1 proves `decode_encode` but not a general `encode_decode`. The G3-B4 requirement therefore makes the S2 transcript codec stricter than S1's instance codec. That is intended. Its purpose is non-malleability of `tB`; it is not needed for soundness of the checked proposition.

---

## 1. Claim of record

Relative to (a) a frozen `InstanceCommitment`; (b) the concrete profile artifact bound by `profile_digest` (§6a), including `KeyResolutionV0` and the S1 verifier-manifest digest; (c) the committed log identity; (d) a presented, validly signed checkpoint `S_R` (TB6); and (e) a log view `V` of `L` through `S_R` together with a transcript `T` for which `TranscriptFaithful(T, V)` holds (TB2), S2 establishes:

> The evidence value `e` and the claim in the S1 instance bytes checked by the S1 certificate — whose semantic profile is the projection of the committed concrete profile — are exactly: the commitment's claim, and `Bundleπ` of every valid, registered, in-scope `RelevantAdmission` for the instance in `V` before the unique valid owner closure. No `RelevantAdmission` for the instance exists in `V` after that closure and before `size(S_R)`.

S2 does **not** establish that:

- all evidence existing in the world was registered;
- all relevant evidence exists in the committed log `L`;
- no other request, sibling instance, or other-log instance exists;
- the issuer was ignorant of unregistered or out-of-scope evidence;
- the Transparency Service is non-equivocating (assumed, TB3);
- `S_R` is fresh, or anything registered after `S_R` is absent (TB6).

## 2. Why S2 is necessary

Unchanged from v0.2. Under monotone compatibility, omitting admissions can only enlarge the compatible-world set; an issuer can manufacture `NotDemonstrated(reason=underdetermined)` by withholding a determining admission (strategic abstention).

- `A1 = first false`, `A2 = second false`, both valid, registered, authorized, same instance.
- `Bundle([A1]) = obs false none` — Underdetermined for `secondBit`.
- `Bundle([A1, A2]) = obs false (some false)` — Determinate for `secondBit`.
- Closure references `[A1]`. S1 alone accepts. S2 MUST reject. This is **S2-N0**.

## 3. Repository split

Unchanged from v0.2. S2a `p10-coverage-lean-s2` (kernel-checked), S2b `p10-replay-verifier` (tested TCB), S3 `p10-scitt-s3` (external service, captured vectors). One-way dependencies. **This prereg authorizes S2a only.**

**[A6: D-S3]** S3, when authorized, MUST use a Transparency Service whose verifiable data structure is `RFC9162_SHA256` (COSE Receipts VDS `1`), because profile v0.1.1 `FullPrefixReplay` reconstructs that root. A service using another VDS (for example the CCF ledger VDS) is outside this profile instance. Using another VDS would require a different or future P10 profile (or profile version) that normatively permits that VDS; changing only the S2a instance cannot make it conformant to profile v0.1.1 **[A6: G7-B2]**.

## 4. Trust boundaries

**TB0 — Lean kernel and toolchain.** Inherited from S1, pinned (Lean 4.33.0).

**TB1 — S1 semantics.** S2 MUST NOT redefine `Profile`, `Compatible`, `Eval`, `Underdetermined`, `CertificateTargetV0`, `Bound`, `Wπ`, `Eπ`, or the S1 wire codec.

**TB2 — Transcript producer (S2b).** Lean models the log as an abstract `LogView`:

```lean
structure LeafFacts (Item : Type) where
  sub : Subject            -- canonical protected CWT sub bytes
  iss : Iss
  kind : Kind
  sig : SigObservation     -- pure cryptographic observation, see below
  payload : Option (Payload Item)

structure LogView (Item : Type) where
  size : Nat
  leaf : Nat → Option (LeafFacts Item)   -- none = not obtainable by the verifier
```

```lean
inductive SigObservation
  | verified         -- KeyResolutionV0 assigns a key to iss, and the signature verifies under it
  | badSignature     -- a key is assigned, and the signature does not verify
  | keyUnavailable   -- no key obtainable for iss (not in KeyResolutionV0, or material missing)
```

S2b reports `SigObservation` for every subject leaf and consults nothing but `KeyResolutionV0`. It never decides whether an `iss` is authorized. Lean combines the observation with the committed `iss` set and owner identity (§6).

`TranscriptFaithful(T, V)` is a Lean `Prop` stating that `T.checkpoint.size = V.size` and that every row and detailed entry of `T` agrees with `V.leaf` at its index, including availability. Lean cannot discharge it. S2b's obligation is that the real log `L` at `S_R` is a `LogView` `V` with this property: that the leaves reconstruct `root(S_R)` under `LeafEncodeV0`, that `S_R` is signed by the committed checkpoint key, and that `sub`, `iss`, `kind`, `payload`, and `sig` are read and observed correctly. The premise appears as the hypothesis `hFaithful` in §9. It is never absorbed.

**TB3 — Transparency Service.** Non-equivocation and uniqueness of the log view at `S_R` are assumed. The fixture's order-independent bundle removes within-batch order from the epistemic TCB. Lifecycle ordering uses leaf index.

**TB4 — Identity and key resolution.** Two separate frozen objects:

1. `authorized_admitter_set_digest` (in `InstanceCommitment`, profile §2.3) binds exactly the canonical set of permitted admitter CWT `iss` values. S2 does not change its meaning. **[A: B3]** The set is the explicit `pB.authorized_admitters` field (§6a). It is never derived from `KeyResolutionV0`. Lean authorization uses only this set and the owner identity. `KeyResolutionV0` is used only by S2b for `SigObservation`. An `iss` that has a key in `KeyResolutionV0` but is not in `authorized_admitters` is unauthorized. An authorized `iss` without a key produces `keyUnavailable` → HALT (TB5).
2. **[A: G6-B2]** `KeyResolutionV0` is a separate canonical mapping from the `iss` values for which frozen verification-key material is available to their key fingerprints. Membership in the map grants no authorization. An authorized admitter or the owner absent from the map yields `keyUnavailable` → HALT (TB5, S2-N31). The concrete profile π contains it as part of its "lifecycle/admitter authorization" rules, which profile v0.1.1 §1(1) and §2.2 require to be frozen and digested before evidence admission. It is therefore bound by `profile_digest`.

Dynamic resolution (DID updates, rotation, mutable trust anchors) is inadmissible in S2 v0. S2a checks, inside `coverageCheck` (C1), that the key-resolution digest S2b used equals the digest of `pB.key_resolution`, and that `SHA-256(pB)` equals the committed `profile_digest` (§6a). If ratification finds that `profile_digest` does not bind `KeyResolutionV0` without amending the profile, S2 HALTs under stop condition 3.

**TB5 — Availability.** Any leaf or protected header in `[0, size(S_R))` that is not obtainable → HALT, whether or not it would have matched the subject; unavailability of that data is exactly what prevents knowing. A subject entry's payload that is not obtainable → HALT. Missing checkpoint material → HALT. `keyUnavailable` for an `iss` that Lean finds authorized (admitter set or owner) → HALT. For an unauthorized `iss` it is not an availability event. Payloads of non-subject leaves are not required. Absence is never evidence of absence.

**TB6 — Checkpoint selection and freshness.** S2 proves historical completeness only through the presented, validly signed `S_R`. It proves no freshness. If a party with an omission incentive controls which `S_R` is presented, selecting a stale checkpoint (before a later admission) remains outside the S2 guarantee. Freshness requires an external mechanism such as verifier-chosen checkpoints, witness cosigning, or a freshness policy. Such a mechanism is out of scope for S2 v0.

**TB7 — Verifier identity.** The acceptance harness recomputes `VerifierManifestS2aV0` for the running build, resolves `pB.verifier_manifest_ref`, and checks that both digests equal `pB.verifier_manifest_digest`. Mismatch → REJECT. The referenced manifest is unavailable → HALT (profile M33). This mirrors the S1 statement-level check (profile M35) and is not a Lean result.

## 5. Profile decisions for S2 v0

1. `KeyResolutionV0` is a field of the committed profile artifact `pB` and frozen before the first admission (TB4). `authorized_admitter_set_digest` remains an `iss` set.
2. The fixture `Bundleπ` is order-independent, idempotent, total, and faithful to a frozen per-item relation (§13).
3. Leaf index is authoritative for lifecycle ordering.
4. S2a consumes canonical transcript bytes `tB` and profile-artifact bytes `pB` as inputs, each SHA-256-bound to the checked proposition.
5. Signature validity enters only as `SigObservation` under TB2. Lean never claims to prove it.
6. S2 v0 is fixture-scale. One row per leaf is required. Scaling is out of scope.

## 6. Core formal objects

Conceptual surface; names may change, semantics may not.

```lean
structure AdmissionProfile extends P10.Profile where
  Item        : Type
  admissible  : Item → Bool                  -- AdmissibleItemπ
  itemCompat  : Item → World → Bool          -- frozen per-item relation (§13)
  bundle      : List Item → Evidence         -- Bundleπ, total

inductive Kind | profileCommit | instanceCommit | admission | closure | adjudication

inductive RowStatus
  | available (sub : Subject)                -- canonical protected sub bytes
  | unavailable                              -- leaf/header not obtainable → HALT

structure Row where
  idx    : Nat
  status : RowStatus

structure DetailedEntry (Item : Type) where
  idx     : Nat
  iss     : Iss
  kind    : Kind
  sig     : SigObservation                 -- from S2b, uninterpreted
  payload : Option (Payload Item)          -- none = not obtainable

structure Checkpoint where
  size       : Nat
  rootDigest : Digest

structure Transcript (Item : Type) where
  logIdentityDigest   : Digest
  keyResolutionDigest : Digest               -- digest of the KeyResolutionV0 S2b used
  checkpoint          : Checkpoint           -- S_R
  rows                : List Row             -- exactly one per index in [0, size)
  detailed            : List (DetailedEntry Item)  -- every available row whose sub matches

inductive CoverageOutcome (Evidence : Type)
  | accept (e : Evidence)
  | reject (r : RejectReason)
  | halt   (r : HaltReason)                  -- carries no Evidence
```

Rules decided in Lean:

- `rows.map idx = [0, …, checkpoint.size - 1]`. A missing, duplicated, or extra index → REJECT (malformed or truncated).
- **Any** row with status `unavailable` anywhere in `[0, size)` → HALT (after C1). The index is present, the data is not, so Lean cannot know whether the leaf is a subject leaf.
- Every `available` row whose `sub` bytes equal the instance subject bytes has exactly one `DetailedEntry` with the same `idx`, and vice versa. Otherwise REJECT.
- `logIdentityDigest = commitment.log_identity_digest`, `SHA-256(pB) = commitment.profile_digest`, and the remaining §6a checks on `pB`. Otherwise REJECT.
- Authorization and signature validity are decided in Lean, in this order:

| `iss` role (Lean, from committed set / owner) | `sig` (S2b) | Lean classification |
|---|---|---|
| authorized admitter, or owner for lifecycle kinds | `verified` | signature valid |
| authorized admitter, or owner | `badSignature` | invalid; cited → REJECT |
| authorized admitter, or owner | `keyUnavailable` | HALT |
| neither | any | unauthorized: not a `RelevantAdmission`, not an owner lifecycle entry; cited → REJECT; never HALT |

### 6a. Concrete profile artifact, verifier manifest, and their binding

S1 instance bytes do not carry the concrete profile: `P10.Wire.Instance` has only `claim, evidence, w0, w1`, and the S1 verifier-manifest digest is not in `iB`. The binding is built on the S2 side, as a chain:

```text
InstanceCommitment.profile_digest
      = SHA-256(pB)                       -- checked in Lean (C1)
pB : ProfileArtifactS2V0 (canonical bytes, checker INPUT)
      .verifier_manifest_digest
      = digest(VerifierManifestS2aV0)     -- checked by acceptance harness (TB7)
VerifierManifestS2aV0
      → S2a checker sources, toolchain, .olean set, axiom policy, acceptance command
      → frozen S1 dependency: tag v0.1.0-s1-ratified, commit e4db3747…, S1 manifest digest
```

**`ProfileArtifactS2V0` — exact schema.** It is canonical JSON with exactly these fields; a missing, extra, duplicated, or non-canonical field → decode failure:

| Field | Content |
|---|---|
| `artifact_version` | `"P10-S2-ProfileArtifact-v0"` |
| `normative_profile_digest` | SHA-256 of Underdetermination Profile v0.1.1 (equals S1 `specTok`) |
| `s1_profile_token` | `"p10-s1-toy-v0"` (equals S1 `profileTok`) |
| `fixture_id` | S2 fixture identifier and version |
| `verifier_manifest_ref` | locator of `VerifierManifestS2aV0` |
| `verifier_manifest_digest` | SHA-256 of canonical `VerifierManifestS2aV0` bytes |
| `key_resolution` | canonical `KeyResolutionV0` (`iss` → key fingerprint) |
| `authorized_admitters` **[A: B3]** | canonical JSON array of the authorized admitter `iss` strings, strictly ascending (hence duplicate-free); the owner `iss` is not in it |
| `log_identity_scheme` | `"LogIdentityV0"` |
| `leaf_encoding` | `"LeafEncodeV0"` |
| `leaf_encoding_spec_digest` **[A: B4, G6-B3]** | `LeafEncodeSpecArtifactDigestV0` of the frozen `LeafEncodeV0` specification file (manifest-covered; see §6b) |
| `subject_derivation` **[A: B2]** | `"SubjectDeriveV0"` |
| `checkpoint_vds` | checkpoint key/VDS algorithm identifier |
| `evidence_scope_rule_id`, `admission_rule_id`, `coverage_rule_id` | identifiers of the frozen rules |

**`VerifierManifestS2aV0` — exact schema.** Canonical JSON with exactly these fields; missing, extra, duplicated, or non-canonical → invalid manifest (TB7 REJECT):

| Field | Content |
|---|---|
| `manifest_version` | `"P10-S2a-VerifierManifest-v0"` |
| `lean_toolchain_identifier` | `"leanprover/lean4:v4.33.0"` |
| `lean_toolchain_artifact_digest` | SHA-256 of the exact toolchain artifact |
| `checker_source_tree_digest` | SHA-256 of the canonical encoding of `checker_source_files` |
| `checker_source_files` | path → SHA-256 for every source file in the manifest-covered Lean checker library **and** every acceptance-harness source or script that implements TB7, manifest verification, partition checking, vector-manifest verification, or acceptance orchestration. Excludes concrete `pB`, vector, and test bytes. |
| `dependency_lock_digest` | SHA-256 of `lake-manifest.json` and `lean-toolchain` |
| `build_manifest_digest` | SHA-256 of `lakefile` and build configuration |
| `checker_olean_digest_set` | path → SHA-256 for every `.olean` of the manifest-covered library, and nothing else |
| `axiom_policy_digest` | digest of the axiom policy and acceptance-policy files |
| `acceptance_command_digest` | SHA-256 of the exact acceptance command |
| `frozen_dependencies` | exactly `{ "s1_tag": "v0.1.0-s1-ratified", "s1_peeled_commit": "e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1", "s1_verifier_manifest_digest": <SHA-256 of VerifierManifestS1.json at that commit> }` |

The eight binding fields after `manifest_version` use the normative `VerifierManifestV0` names (profile v0.1.1). `manifest_version`, `checker_source_files`, and `frozen_dependencies` are S2 additions. The path lists `checker_source_files` and `checker_olean_digest_set` are mandatory fields of the exact schema; there is no optional variant.

Including the harness in `checker_source_files` does not reintroduce a hash cycle: harness code checks its input generically and embeds no concrete `verifier_manifest_digest`, and the manifest never contains its own digest. Without it, `acceptance_command_digest` would bind only the command line (e.g. `./scripts/verify.sh`), not the bytes of the script that performs TB7.

**Partition rule (prevents the hash cycle).** No module whose source or `.olean` is covered by `VerifierManifestS2aV0` may, directly or transitively, embed or depend on bytes that contain `verifier_manifest_digest`. That includes any `pB` and any vector containing a commitment with a `profile_digest`. Concretely:

- The manifest covers the checker library: transcript and profile-artifact codecs, `coverageCheck`, fixture semantics (`fx`, `bundle`, `itemCompat`, `admissible`), and the theorem modules of §8–§10 stated over **arbitrary** inputs.
- Vectors, `pB` files, and the Lean test modules that instantiate theorems on concrete vectors (the §11 tests and E2E must-fail files) are a separate Lean library outside the manifest.

**`VectorManifestS2aV0` — second integrity root.** A canonical file (or `S2A_VECTOR_SHA256SUMS`) listing path → SHA-256 for exactly: every `pB` file; transcript and `InstanceCommitment` fixtures; **[A: G6-F]** every vector named in §11 (S2-P1…P3, S2-P2x, S2-N0…N36c, S2-D1, S2-K1…K8 **[A6]**) and every additional implementation variant; every concrete Lean test module and E2E must-fail module; and the expected-result metadata for each vector.

- The digest of `VectorManifestS2aV0` MUST NOT appear in any `pB`, in `VerifierManifestS2aV0`, or in any manifest-covered module. (Every `pB` contains the verifier manifest digest, so a vector-manifest digest fed back would recreate the cycle.)
- The acceptance command (1) verifies every listed digest, (2) rejects if the set of files under the vector/test roots is not exactly the listed set (no unlisted and no missing files), and (3) runs every vector and compares against its expected result. Any failure fails acceptance.
- Root of trust for both manifests: the implementation commit, and later the human-signed S2 ratification tag, which freezes `VerifierManifestS2aV0` and `VectorManifestS2aV0` together. Neither manifest certifies the other.

**How each part is bound.**

- `pB` is an input to `coverageCheck` alongside `T`. C1 checks `SHA-256(pB) = commitment.profile_digest`, decodes `pB` strictly, and checks `fixture_id` equals the compiled fixture constant, `normative_profile_digest = specTok`, `s1_profile_token = profileTok`, and that the transcript's `keyResolutionDigest` equals the digest of `pB.key_resolution`. Every `KeyResolutionV0` lookup Lean performs uses `pB.key_resolution`.
- `fx` is defined as an extension of `P10.S1.profile`, so `fx.toProfile = P10.S1.profile` holds by `rfl`.
- The Lean semantics of `fx` are bound through the manifest (TB7), not serialized.
- **[A: B6]** `claimDigest` is `ClaimDigestV0` (§6b). The v0.2.4 definition `SHA-256(claimTok c)` is withdrawn.
- Lean cannot know the digest of its own build. The equality `pB.verifier_manifest_digest = digest(VerifierManifestS2aV0 of the running build)` is therefore a harness check (TB7), not a Lean theorem.

### 6b. Canonical digests and descriptors **[A: B1–B6, I-2, I-3]**

All structured P10 digests below are SHA-256 over JCS (RFC 8785) bytes (profile §2.7). **[A: G6-B3]** `LeafEncodeSpecArtifactDigestV0` is the binary-artifact exception required by profile §2.7: it hashes the frozen format identifier together with the exact raw artifact bytes, with no JCS layer. In S2 v0 every string value is restricted to the S1 token alphabet `[A-Za-z0-9_.:-]` or to lowercase hex. JCS output is therefore the literal skeleton with sorted keys, no whitespace, and no escapes. Lean builds these bytes directly and needs no general JCS implementation. Arrays preserve the order given; where a set is meant, the order is strictly ascending by byte value.

| Name | JCS object | Used for |
|---|---|---|
| `ClaimDigestV0(c)` **[B6]** | `{"claim": claimTok c}` | `claim_digest`; §9 |
| `EvidenceDigestV0(e)` **[B1]** | `{"evidence": evidenceTok e}` (S1 token, defined for every `Evidence` constructor) | `closed_evidence_set_digest`; exposed for S3 `evidence_digest` |
| `AuthorizedAdmittersDigestV0(A)` **[B3]** | `{"authorized_admitters": [iss…]}`, strictly ascending | `authorized_admitter_set_digest` |
| `KeyResolutionDigestV0(K)` **[I-3]** | `{"key_resolution": K}` in the `pB` canonical form | transcript `keyResolutionDigest` |
| `PreclosureDigestV0(v)` **[I-2, A6: K-1]** | `{"preclosure_view": [[idx, kind, iss], …]}`; `idx` is the canonical decimal string (no sign, no leading zeros except `"0"`); `kind` is the token from the kind-token table below, never a Lean constructor name; `iss` is the entry's canonical `iss` token (for an owner lifecycle entry, view membership requires `iss = inst.instance_owner_iss`, bound by `InstanceCommitment`; for a relevant admission, `iss` MUST be a member of `pB.authorized_admitters`) **[A6: G7-B1]**; entries in leaf order (not sorted); empty view is `{"preclosure_view":[]}`; `v` is the `ClosureTranscriptViewπ` subsequence before the closure leaf (definition of the view unchanged from implementation note I-5) | `checkpoint_preclosure_transcript_digest` |
| `SubjectDeriveV0(i, r)` **[B2]** | `"p10s2sub:" ++ hex(SHA-256(JCS({"issuer_id": i, "request_id": hex(r), "v": "SubjectDeriveV0"})))` — a `tstr` | `instance_subject` |
| `SubjectDerivationDigestV0` **[B2, B4]** | `{"rule": "SubjectDeriveV0", "verifier_manifest_digest": pB.verifier_manifest_digest}` | `subject_derivation_digest` |
| `LeafEncodeSpecArtifactDigestV0(f)` **[G6-B3]** | **not JCS** — binary-artifact rule: `SHA-256("P10-LeafEncodeSpecArtifact-v0:" ++ "text-markdown-utf-8-v0:" ++ f)`, where both prefixes are fixed ASCII bytes and `f` is the exact raw file bytes | `pB.leaf_encoding_spec_digest` |
| `LeafEncodingProfileDigestV0` **[B4]** | `{"rule": "LeafEncodeV0", "spec_digest": pB.leaf_encoding_spec_digest}` | `leaf_encoding_profile_digest` |
| `EvidenceScopeDigestV0` **[B4]** | `{"rule": pB.evidence_scope_rule_id, "verifier_manifest_digest": pB.verifier_manifest_digest}` | `evidence_scope_digest` |
| `AdmissionRuleDigestV0` **[B4]** | `{"rule": pB.admission_rule_id, "verifier_manifest_digest": pB.verifier_manifest_digest}` | `admission_rule_digest` |
| `CoverageRuleDigestV0` **[B4]** | `{"rule": pB.coverage_rule_id, "verifier_manifest_digest": pB.verifier_manifest_digest}` | `coverage_rule_digest` |

**Kind-token table [A6: K-1].** Normative. The left column names the S2a Lean constructors at HEAD `fbcfefa` for traceability only; the right column is what is hashed, and it does not change if a constructor is renamed.

| `Kind` constructor (informative) | JCS token (normative) |
|---|---|
| `profileCommit` | `"profile_commit"` |
| `instanceCommit` | `"instance_commit"` |
| `admission` | `"admission"` |
| `closure` | `"closure"` |
| `adjudication` | `"adjudication"` |

All `iss` values that can appear in a view are the owner or an authorized admitter. The lifecycle-owner `iss` is frozen by `InstanceCommitment`; authorized-admitter `iss` values are frozen by `pB.authorized_admitters` **[A6: G7-B1]**. C1 decoding already restricts them to the §6b token alphabet.

**Why descriptors carry the verifier-manifest digest [B4].** Profile §2.7 states that noncryptographic or merely immutable identifiers are insufficient. A rule name alone would bind nothing. The scope, admission, coverage, and subject-derivation rules are executed by the S2a checker, whose source and `.olean` files are covered by `VerifierManifestS2aV0`. Including that digest therefore binds the executed rule content. There is no cycle: the descriptors live in `pB` and in the commitment, and neither is manifest-covered (§6a partition).

**`LeafEncodeV0` [B4].** S2a does not execute leaf encoding (S2b does). S2a therefore binds *which* specification is committed: the `LeafEncodeV0` specification is a frozen, manifest-covered file, and **[A: G6-B3]** `pB.leaf_encoding_spec_digest` is `LeafEncodeSpecArtifactDigestV0` of it: the exact raw file bytes are hashed directly together with the frozen format identifier `text-markdown-utf-8-v0` (media type `text/markdown; charset=utf-8`, UTF-8, no BOM), under a fixed domain prefix, as profile §2.7 requires for binary artifacts. Both prefixes are fixed, so the byte layout is unambiguous. Execution conformance is an S2b obligation (TB2) and is not claimed by S2a.

**[A6: L-1]** The committed specification file MUST define a complete byte mapping: input bytes, the single admissible format identifier, the exact leaf-input layout, and normative test vectors. A specification that states it defines no concrete mapping is a placeholder. A `pB` binding a placeholder is not admissible for S2a ratification. S2a acceptance still checks only the digest binding, not the mapping's execution.

**`log_identity_digest`.** Unchanged: S2a checks equality between the commitment and the transcript. Recomputing `LogIdentityV0` from `ts_iss`, the checkpoint key fingerprint, and the VDS algorithm is S2b's job. S2a does not claim it (§16).

**Differential check.** For at least P1, `ClaimDigestV0` and `EvidenceDigestV0` computed in Lean MUST equal the values produced by frozen S1 tooling (`scripts/p10tool.py`, `sha256_bytes(jcs({"claim": …}))`, `jcs({"evidence": …})`) for the same tokens. This is a recorded vector, not a runtime dependency.

## 7. Coverage acceptance condition

`coverageCheck π inst T = .accept e` iff all hold:

| # | Condition | On failure |
|---|---|---|
| C1 | Identity, key-resolution, profile-digest, and contiguity rules (§6, §6a) | REJECT |
| C1a **[A: B2]** | `inst.instance_owner_iss = inst.issuer_id`, and `inst.instance_subject = SubjectDeriveV0(inst.issuer_id, inst.request_id)` | REJECT |
| C1b **[A: B3]** | `inst.authorized_admitter_set_digest = AuthorizedAdmittersDigestV0(pB.authorized_admitters)`; transcript `keyResolutionDigest = KeyResolutionDigestV0(pB.key_resolution)` **[A: I-3]** | REJECT |
| C1c **[A: B2, B4]** | `inst.subject_derivation_digest`, `inst.leaf_encoding_profile_digest`, `inst.evidence_scope_digest`, `inst.admission_rule_digest`, `inst.coverage_rule_digest` each equal the §6b descriptor digest computed from `pB` | REJECT |
| C2 | No row in `[0, size)` is `unavailable`; no subject entry has `payload = none`; no authorized/owner entry has `sig = keyUnavailable` | HALT |
| C3 **[A: G6-B1]** | Exactly one valid owner-signed profile commitment for `instance_subject` exists in `[0, size(S_R))`; its digest equals `inst.profile_digest`; it precedes the first `RelevantAdmission` (M5, M19, profile §1(2)) | zero → HALT; ≥2 (same or different digest) → REJECT; digest ≠ `inst.profile_digest` → REJECT; after first admission → REJECT |
| C4 | Exactly one valid owner-signed `InstanceCommitment` for the tuple, before the first `RelevantAdmission`, with one `profile_digest` and one `claim_digest` (M7, M13, M15, M19) | zero → HALT; ≥2 or conflicting → REJECT |
| C5 | Lifecycle entries with `iss ≠ instance_owner_iss` are excluded from counts; if cited by a valid object → REJECT (M28) | REJECT |
| C6 | Exactly one valid owner closure; validity includes the `checkpoint_preclosure_transcript_digest` rule (M29), computed as `PreclosureDigestV0` **[A: I-2]** | zero valid → HALT; ≥2 valid → REJECT |
| C7 | Refs strictly ascending, no duplicates | REJECT |
| C8 | Every ref is a `RelevantAdmission`: matching `sub` bytes, `kind = admission`, `iss` authorized, `sig = verified`, `admissible = true`. A ref to a `badSignature` entry, an unauthorized entry, or a non-admissible item → REJECT (M20) | REJECT |
| C9 | Every `RelevantAdmission` with `idx < closure.idx` appears in the refs exactly once (M21) | REJECT |
| C10 | No `RelevantAdmission` with `closure.idx < idx < checkpoint.size` (M22) | REJECT |
| C11 **[A: B5]** | At least one valid owner-signed adjudication entry with `closure.idx < idx < checkpoint.size` exists, and **every** such entry has `profileRef = p`, `commitRef = ci`, `closureRef = k`, where `p`, `ci`, `k` are the entries selected by C3, C4, C6 | none → HALT; any such entry with a different ref → REJECT |
| C12 | `e = bundle (items refs)` and `π.inE e` | `e ∉ Eπ` → REJECT |
| C13 **[A: B1]** | `closure.closed_evidence_set_digest = EvidenceDigestV0(e)` for the `e` of C12 | REJECT |

Evaluation order is part of the specification: C1 (malformed or foreign transcript), including C1a–C1c **[A]**, precedes C2 (availability). A malformed transcript therefore REJECTs even if it also marks data unavailable.

## 8. Primary theorem target

```lean
theorem coverage_sound :
  coverageCheck π inst T = .accept e → CoverageSpecT π inst T e

theorem coverage_sound_view :
  TranscriptFaithful T V →
  coverageCheck π inst T = .accept e → CoverageSpecV π inst V e
```

`CoverageSpecT` states C1–C13 (including C1a–C1c) over `T`. **[A: G6-F]** `CoverageSpecV` states the same properties over the log view `V`, in particular:

```text
ProfileBeforeFirstAdmission V inst
∧ UniqueCommitmentBeforeFirstAdmission V inst
∧ UniqueValidOwnerClosure V inst
∧ refs = RelevantAdmissionsBefore V closure.idx      -- as lists, ascending
∧ NoRelevantAdmissionIn V (closure.idx, V.size)
∧ e = π.bundle (items refs) ∧ π.inE e
```

**[A: B1–B5]** `CoverageSpecT` and `CoverageSpecV` additionally state C1a–C1c, the C11 ref equalities, and C13, as propositions. `coverage_sound` and `coverage_sound_view` are re-proven with these conjuncts. No other change to their statements.

A converse (`CoverageSpecT → accept`) is RECOMMENDED, not required for S2a v0.

## 9. Composition theorem with S1 (byte-level)

```lean
theorem s2_end_to_end
    (hT        : decodeTranscript tB = some T)
    (hPB       : decodeProfileArtifact pB = some prof)
    (hFaithful : TranscriptFaithful T V)
    (hCov      : coverageCheck fx inst pB T = .accept e)
    (hS1       : P10.Bound iB (P10.Sha256.sha256 iB))
    (hDec      : P10.Wire.decode iB = some si)
    (hEv       : si.evidence = e)
    (hC        : si.claim = c ∧ ClaimDigestV0 c = inst.claimDigest) :   -- [A: B6]
    CoverageSpecV fx inst V e ∧
    inst.profileDigest = sha256 pB ∧ prof.fixture_id = fxId ∧
    Underdetermined P10.S1.profile e c
```

Requirements:

- The three links are separate and none is extracted from `iB` beyond what S1 decodes:
  - **S1 bytes:** `hS1`, `hDec` — S1 checked `si` under `P10.S1.profile`; S1's decoder already enforces the S1 `kind/profile/spec` constants.
  - **Commitment → concrete profile:** `inst.profileDigest = sha256 pB` and `prof.fixture_id = fxId` are *conclusions* derived from `hCov` via C1 (§6a), not hypotheses. The link from `pB` to the running checker is TB7 (harness).
  - **Semantic projection:** `fx.toProfile = P10.S1.profile` by `rfl` (§6a), used inside the proof.
- `hEv` and `hC` are equalities the end-to-end checker establishes by decoding `iB` and comparing with `e` and `inst.claimDigest`. They are not trusted assertions (S1 M34 pattern). The final checker-owned statement is `∃ si, decode iB = some si ∧ si.evidence = e ∧ …`, produced by computation.
- The theorem MUST use `hCov` and `hFaithful`. Deleting either MUST make it unprovable or weaken its conclusion to exclude `CoverageSpecV`.
- **S2-N0 is a must-fail against this theorem.** With the S2-N0 transcript (forcing `e = obs false (some false)`) and the S1 bytes for `obs false none`, a file asserting `s2_end_to_end` MUST NOT compile.

S1 remains the semantic authority for `Underdetermined`. No `profileBindingOf iB` function exists (G3-B3).

## 10. HALT invariant

- Type-level: `CoverageOutcome.halt` carries no `Evidence`.
- `p10Verdict (.halt r) s = none` and `p10Verdict (.reject r) s = none` for all `r`, `s`.
- No TB5 source reaches `accept` or a verdict.

## 11. Mandatory negative and control tests

| ID | Scenario | Expected |
|---|---|---|
| **S2-N0 (E2E)** | `A1 = first false`, `A2 = second false`, closure `[A1]` | REJECT (C9); §9 must-fail with S1 bytes of `obs false none` |
| S2-N1 | Any valid `RelevantAdmission` before closure omitted | REJECT (C9) |
| S2-N2 | Duplicate ref | REJECT (C7) |
| S2-N3 | Refs not ascending | REJECT (C7) |
| S2-N4 | Matching `sub`, `iss` outside authorized set; cited by closure | REJECT (C8); uncited → excluded |
| S2-N5 | `RelevantAdmission` after closure, before `size(S_R)` | REJECT (C10) |
| S2-N6a / N6b | Zero commitments / two or conflicting | HALT / REJECT (C4) |
| S2-N7 | Subject payload unavailable; checkpoint material missing; `keyUnavailable` for an authorized admitter or owner entry | HALT (C2) |
| S2-N8 | Log identity digest mismatch | REJECT (C1) |
| S2-N9 | `keyResolutionDigest ≠ digest(profile.KeyResolutionV0)` | REJECT (C1) |
| S2-N10 | Valid admission for a sibling subject | Excluded; no effect |
| **S2-N11 (E2E)** | Row indices stop at the closure leaf while `checkpoint.size` is larger | REJECT (C1) |
| S2-N12 | Admission between pre-closure transcript and closure leaf | candidate invalid; no other valid closure → HALT (C6) |
| S2-N13 | Profile commitment absent / after first admission | HALT / REJECT (C3) |
| S2-N14 | Non-owner lifecycle entry cited | REJECT (C5) |
| S2-N15 | Ref to a `badSignature` entry | REJECT (C8) |
| **S2-N16** | Every index present; **one** row `unavailable` (any index, subject or not) | HALT (C2), never REJECT, never accept |
| S2-N18 | Unauthorized `iss` subject entry with `sig = keyUnavailable`, uncited | excluded; outcome unaffected; **not** HALT |
| S2-N19 | `commitment.profile_digest ≠ SHA-256(pB)` | REJECT (C1) |
| S2-N20 | `pB` identical except `verifier_manifest_digest` differs from the running build's `VerifierManifestS2aV0` (commitment re-digested accordingly, including the §6b descriptor digests that contain the manifest digest **[A: B4]**) | REJECT (TB7 harness) |
| S2-N21 | `pB.verifier_manifest_ref` does not resolve | HALT (TB7, profile M33) |
| S2-N22 | `pB` with a correct digest but a different `fixture_id`, `normative_profile_digest`, or `s1_profile_token` | REJECT (C1) |
| S2-N23 | `pB` with an extra or missing field, or a non-canonical encoding | REJECT (C1, strict decode) |
| S2-N17 | Row `sub` bytes differ from instance subject by one byte; entry would otherwise be relevant | not in subject view; if cited → REJECT (C8) |
| **S2-P1** | commitment, `A1`, `A2`, closure `[A1, A2]`, adjudication | `accept (obs false (some false))`; S1 finds `Determinate` |
| **S2-P2** **[A: I-1]** | commitment, `A1`, closure `[A1]`, owner adjudication with correct refs | `accept (obs false none)`; §9 holds |
| S2-P2x **[A: I-1]** | as P2 without adjudication | HALT (C11) |
| **S2-P3 (masking control)** **[A: I-1]** | `A1 = first false`, `A3 = first true`, closure `[A1, A3]`, owner adjudication with correct refs | `accept inconsistent`; S1 cannot certify. Closure `[A1]` → REJECT (C9) |
| S2-N24 **[A: B1]** | Valid P1 except `closed_evidence_set_digest` changed | REJECT (C13) |
| S2-N25 **[A: B1]** | Valid P1 except `closed_evidence_set_digest = EvidenceDigestV0(obs false none)` while refs are `[A1, A2]` (digest of an omitted-evidence bundle) | REJECT (C13) |
| S2-N26 **[A: B2]** | `instance_owner_iss ≠ issuer_id`, everything else consistent | REJECT (C1a) |
| S2-N27 **[A: B2]** | `instance_subject ≠ SubjectDeriveV0(issuer_id, request_id)`, log built consistently around that subject | REJECT (C1a) |
| S2-N28a–e **[A: B2, B4]** | one each: wrong `subject_derivation_digest`, `leaf_encoding_profile_digest`, `evidence_scope_digest`, `admission_rule_digest`, `coverage_rule_digest` | REJECT (C1c) |
| S2-N29 **[A: B3]** | `authorized_admitter_set_digest` ≠ digest of `pB.authorized_admitters` | REJECT (C1b) |
| S2-N30 **[A: B3]** | `iss` has a key in `KeyResolutionV0` but is not in `authorized_admitters`; its admission is cited by the closure | REJECT (C8) |
| S2-N31 **[A: B3]** | `iss` in `authorized_admitters` has no key in `KeyResolutionV0`; its subject entry has `sig = keyUnavailable` | HALT (C2) |
| S2-N32a–c **[A: B5]** | valid owner-signed adjudication after closure with wrong `profileRef` / `commitRef` / `closureRef` | REJECT (C11) |
| S2-N32d **[A: B5]** | one correct and one wrong-ref valid owner adjudication after closure | REJECT (C11) |
| S2-N33 **[A: B6]** | `claim_digest = SHA-256(claimTok c)` (the withdrawn v0.2.4 form) | §9 end-to-end fails; composed verdict none |
| S2-N34 **[A: I-2]** | closure whose preclosure digest uses the old binary form | closure invalid → no valid closure → HALT (C6) |
| S2-N35 **[A: I-3]** | transcript `keyResolutionDigest` in the old binary form | REJECT (C1b) |
| S2-N36a **[A: G6-B1]** | two valid owner profile commitments, same digest | REJECT (C3) |
| S2-N36b **[A: G6-B1]** | two valid owner profile commitments, conflicting digests; commitment and adjudication reference the first | REJECT (C3) |
| S2-N36c **[A: G6-B1]** | exactly one owner profile commitment whose digest ≠ `inst.profile_digest` | REJECT (C3) |
| S2-K1 **[A6: K-1]** | `PreclosureDigestV0([])`; bytes `{"preclosure_view":[]}` | `f6a13471a3d83b209e20d032e009f9b34ec8ccf08d4f35e00f076b3694901049` |
| S2-K2 | `[["0","profile_commit","owner"]]` | `e6df04feb34214b662d882472345eb72a3f6fbbf2912083db34f19acfe67ca32` |
| S2-K3 | `[["1","instance_commit","owner"]]` | `6c65a27b6f951633302cba21f4760ef6b7fd15fbfc52ba761a2fbaf09c973dd3` |
| S2-K4 | `[["2","admission","admitter-a"]]` | `d8cb3193f9cd3a2d582a3f809da910e8dbe72c905bdfca29e5235d35c432bf6a` |
| S2-K5 | `[["3","closure","owner"]]` | `3adcfe25eaea80607375e1575e657b5270332cc1c5911212f1a4cadfbd86f804` |
| S2-K6 | `[["4","adjudication","owner"]]` | `6ff98382828faca48de0bc2ace1eb233043a48d660291cb9516cf4b85420c956` |
| S2-K7 | `[["0","profile_commit","owner"],["7","instance_commit","owner"],["10","admission","admitter-a"],["123","admission","admitter-b"]]` — leaf order is preserved: `"7"` remains before `"10"`; lexicographic sorting would incorrectly place `"10"` before `"7"` **[A6: G7-F2]** | `679708f452ee69dde496ddc5b381383ae02f410930f2dc19ef5406710a44f87f` |
| S2-K8 | Lean `PreclosureDigestV0` on the K1–K7 views equals an independent Python JCS computation | equal |
| S2-D1 **[A: B6, B1]** | differential vector: Lean `ClaimDigestV0`, `EvidenceDigestV0` for P1 equal frozen S1 tooling output | equal |

## 12. Positive control acceptance

S2-P1 and S2-P2 each produce exactly one canonical evidence value and `accept`. S2-P2 composes with S1 under §9.

## 13. Fixture: items, per-item relation, bundle

```lean
inductive Item | first (b : Bool) | second (b : Bool)

def itemCompat : Item → World → Bool
  | .first b,  w => firstBit w == b
  | .second b, w => secondBitOf w == b

-- order-independent, idempotent, total
bundle xs :=
  let F := {b | first b ∈ xs}, S := {b | second b ∈ xs}
  if F = ∅                    then Evidence.outside        -- ∉ Eπ → REJECT (C12)
  else if |F| = 2 ∨ |S| = 2   then Evidence.inconsistent   -- ∈ Eπ, no compatible world
  else obs (the F) (S.toOption)
```

Required fixture theorems:

- `bundle_perm : xs.Perm ys → bundle xs = bundle ys`
- `bundle_dedup : bundle xs.eraseDups = bundle xs`
- **`bundle_faithful`** (G2-B5, exact characterization):
  `π.inE (bundle xs) → ∀ w, π.inW w → (Compatible (bundle xs) w ↔ ∀ x ∈ xs, itemCompat x w = true)`
- `bundle_refines` (G2's law, a corollary of `bundle_faithful`):
  `xs ⊆ ys → π.inE (bundle xs) → π.inE (bundle ys) → ∀ w, π.inW w → Compatible (bundle ys) w → Compatible (bundle xs) w`
- Truth-table cases: `bundle [first false] = obs false none`; `bundle [first false, second false] = obs false (some false)`; conflict cases for `F` and `S` give `inconsistent`; `bundle [] = outside`; `bundle [second b] = outside`.

**Why `bundle_refines` alone is insufficient.** A bundle that silently discards every `second` item is monotone. It satisfies `bundle_refines`, yet it is lossy: S2-N0 would then be accepted with closure `[A1, A2]`, and `e = obs false none` would still certify underdetermination. `bundle_faithful` forbids this, because the compatible set must equal the intersection of the per-item relations. `bundle_refines` is kept as a named corollary.

`itemCompat` is part of the frozen fixture profile. The S1 fixture is not modified: `inconsistent`, `outside`, `obs`, `compatB` are existing S1 definitions. `bundle_faithful` holds only under `π.inE`, which excludes `outside`.

Order-independence and intersection semantics are fixture/profile design choices, not universal P10 requirements. A future profile with non-conjunctive evidence needs its own faithfulness law.

## 14. Stop conditions

Development HALTs before S2b/S3 if any of the following occurs:

1. S2a cannot reject S2-N0 or S2-N11 without relying on S1.
2. The §9 theorem can be stated or proven without using `hCov` or `hFaithful`, or it requires any hypothesis that extracts profile identity from `iB`.
3. `KeyResolutionV0` or `VerifierManifestS2aV0` cannot be bound by `profile_digest` through `pB` without amending profile v0.1.1, or cannot be frozen unambiguously.
9. The §6a partition rule cannot be satisfied, i.e. a manifest-covered module needs bytes that contain a manifest digest.
4. S2a proves cryptographic or network facts that only S2b can supply, or S2b decides authorization or relevance.
5. Any completeness claim survives a transcript that is not contiguous over `[0, size(S_R))`.
6. Any HALT source reaches `accept` or a verdict, or an unavailable row yields REJECT instead of HALT (outside C1).
7. S2 modifies S1 semantics or depends on S1 `main` instead of the ratified tag.
8. `bundle_faithful` fails for the fixture.
10. **[A]** A §6b digest cannot be expressed as JCS over the restricted alphabet, or the gate finds that the B1 or B4 interpretation changes the meaning of a profile v0.1.1 field.

## 15. Acceptance gates

**S2a — ready for adversarial review only after:**

- Clean `lake build`, warnings as errors, Lean 4.33.0, S1 required at `v0.1.0-s1-ratified`.
- No `sorry`, `admit`, `native_decide`, custom axioms, `unsafe`, or equivalent; axiom audit recorded for every exported theorem.
- Proven: `coverage_sound`, `coverage_sound_view`, `s2_end_to_end`, `fx_projection : fx.toProfile = P10.S1.profile`, `bundle_perm`, `bundle_dedup`, `bundle_faithful`, `bundle_refines`, §10 theorems.
- Transcript codec: strict decoder with general laws `decode_encode : decodeTranscript (encodeTranscript T) = some T` and `encode_decode : decodeTranscript b = some T → encodeTranscript T = b` (non-malleability of `tB`). The same laws hold for the `ProfileArtifactS2V0` codec.
- Every §11 row has its expected result. S2-N0 and S2-N11 are E2E must-fail files against §9. **[A]** S2-N24 … N36c, S2-D1, and S2-K1 … K8 **[A6]** are added to `VectorManifestS2aV0`. No commitment or closure in any vector carries a placeholder digest.
- Transcript bytes SHA-256-bound to the checked proposition.
- `TranscriptFaithful`, TB4, and TB6 are documented next to the theorem statements.
- No network or cryptographic library is needed to reproduce the Lean result.
- `VerifierManifestS2aV0` (exact schema) and `VectorManifestS2aV0` are generated and committed; the §6a partition is checked mechanically; the vector file-set equality check runs. The acceptance command fails if any manifest-covered `.olean` imports a module from the vector/test library.
- The TB7 harness check runs as part of the acceptance command, and S2-N20/N21 are exercised by it.

**[A] Implementation note (amendment scope):** the amendment changes binding guards, the §6b digest functions, the `pB` schema (three fields added: `authorized_admitters`, `leaf_encoding_spec_digest`, `subject_derivation` **[A: G6-F]**), and vectors. It does not authorize changes to the bundle theorems, codec laws, §9 structure, the manifest split, or TB7, except where re-proof is forced by the added `CoverageSpec` conjuncts. Implementation note I-16 is withdrawn.

**Implementation note (G3-F2):** the S2 scaffold's placeholder structures (including `InstanceCommitment`) MAY be changed freely to match profile §2.3 and this prereg. No placeholder API is to be preserved.

**S2b — later, not authorized by this prereg:** an independent second implementation of row and entry extraction, differential-tested on the mock log and every mutation vector; the mock log generates S2-N0 … S2-N36c from real COSE/RFC 9162 structures under test keys; S2b also owns execution conformance of `LeafEncodeV0` and recomputation of `LogIdentityV0` **[A: B4]**.

## 16. Claim limitation

Passing S2 means only:

> For this frozen instance, under the committed profile (including its key-resolution policy), authorization set, and transparency-log identity, and given a faithful transcript of the log through the presented checkpoint `S_R`, the evidence and claim certified by S1 are exactly the commitment's claim and the bundle of every valid, registered, in-scope admission for this instance before its unique valid closure, and no such admission was registered between that closure and `S_R`.

It does **not** mean:

> All relevant evidence in existence was considered, or `S_R` is the latest checkpoint.

**[A: B4]** Nor does it mean that `log_identity_digest` was recomputed from the Transparency Service's identity and keys, or that leaves were encoded per `LeafEncodeV0`. S2a checks only that the committed values match the transcript and the committed specification digest. Both are S2b obligations.
