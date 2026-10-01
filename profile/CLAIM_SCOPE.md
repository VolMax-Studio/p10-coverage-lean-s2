# Claim scope (S2a)

What a passing acceptance command establishes is stated in prereg v0.2.6 §1 and §16 (incorporating
v0.2.5 and v0.2.4), reproduced here in substance:

Relative to the frozen `InstanceCommitment`, the concrete profile artifact bound by
`profile_digest`, the committed log identity, a presented checkpoint `S_R`, and a transcript
`T` with `TranscriptFaithful(T, V)`, the evidence and claim certified by S1 are exactly the
commitment's claim and the bundle of every valid, registered, in-scope admission for the
instance before its unique valid closure, with no such admission between the closure and
`size(S_R)`.

It does **not** establish: that all evidence in the world was registered; that the log contains
all relevant evidence; absence of sibling instances or other-log instances; ignorance of the
issuer; transparency-service non-equivocation; `S_R` freshness; anything after `S_R`; or that the
frozen policy/scope/relevance predicate is adequate (coverage is consistency/completeness
relative to it).

**Boundary with S2b (§16, B4).** S2a does not recompute `LogIdentityV0` from the transparency
service identity, checkpoint key and VDS algorithm, and does not execute `LeafEncodeV0`. It checks
only that the committed values match the transcript and the committed specification digest
(`pB.leaf_encoding_spec_digest`, `profile/LeafEncodeV0_SPEC.md`). Execution conformance of
`LeafEncodeV0` and recomputation of `LogIdentityV0` are S2b obligations, and S2b is not authorized.

A green acceptance command is an implementation check. It is neither an adversarial-gate verdict
nor human ratification.
