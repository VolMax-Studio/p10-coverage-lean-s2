# Trust boundaries (S2a)

The authoritative statement is prereg v0.2.6 §4 (TB0–TB7), which incorporates v0.2.5 and v0.2.4. In
this repository:

- **TB0** Lean kernel and toolchain: pinned `leanprover/lean4:v4.33.0` (conda-forge build
  `h6c1889d_0`; the `lean` executable digest is pinned in `scripts/s2a.py` and recorded in the
  verifier manifest).
- **TB1** S1 semantics: untouched; the frozen ratified tag is required (`S1_DEPENDENCY.md`).
- **TB2** Transcript producer (S2b, not authorized here): supplies observations only. Lean decides
  authorization, relevance, lifecycle validity, closure validity, REJECT vs HALT.
  `TranscriptFaithful T V` is the only premise linking `T` to the real log (`CoverageSpec.lean`),
  including that the leaves reconstruct `root(S_R)` under `LeafEncodeV0`.
- **TB3** Transparency service non-equivocation: assumed.
- **TB4** Authorization and key availability are separate. **Authorization:** the owner is bound by
  `InstanceCommitment.instance_owner_iss`; admitters are the explicit `pB.authorized_admitters`
  (digest `AuthorizedAdmittersDigestV0`). **Key availability:** `KeyResolutionV0` in `pB`, digest
  `KeyResolutionDigestV0`. Membership in the key map grants no authorization; an authorized issuer
  with no key yields `keyUnavailable` → HALT (TB5). Both are bound by `profile_digest`.
- **TB5** Availability: any unavailable row / subject payload / authorized key → HALT; never
  evidence of absence.
- **TB6** Checkpoint selection and freshness: no claim about leaves at `idx ≥ size(S_R)`.
- **TB7** Verifier identity: `scripts/s2a.py tb7` (harness), not a Lean theorem.
- **Leaf encoding and log identity (prereg §16, B4).** S2a binds *which* `LeafEncodeV0`
  specification is committed (`pB.leaf_encoding_spec_digest`, the manifest-covered
  `profile/LeafEncodeV0_SPEC.md`) and checks that the commitment's descriptors match it. It does not
  execute `LeafEncodeV0` and does not recompute `LogIdentityV0`; both are S2b obligations.
