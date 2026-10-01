# S2a acceptance report (implementation checks; NOT a gate verdict, NOT ratification)

Recorded by running `P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh` (default serial vector builds,
`P10_VECTOR_JOBS` unset, from a clean build state) at implementation commit
`e153c2af0723f2f33b0a460b408ad1163e963a3a` (exit 0), and by the independent GitHub-hosted CI runs for
the same commit (push and pull-request `verify` jobs, both `success`). In-tree pins prove
self-consistency only; the canonical run takes both pins out of band.

A later documentation-only commit changes this file, the other `profile/*.md` documents, `README.md`
and the D2 provenance note (`P10S2Tests/Gen.lean`, `vectors/D2/expected.txt`); the vector-layer
change alters only `VectorManifestS2aV0`, so the verifier manifest, `pB` files, commitments, spec
digest and all checker code are unchanged. The manifest values below are those of the recorded run;
the final HEAD's pins are in `profile/S2A_PINS.txt`.

- Preregistrations: `S2_PREREG_v0.2.6.md` SHA-256
  `d6fbeb13bf229d0e10c17031a887ef7944ae8e6acc68b6e898a007d5a851c9e0`; `S2_PREREG_v0.2.5.md`
  `e077c30edb33d4799079185ccc4bb3add7e32a5ee4318a358c77a139039c437f`;
  `S2_PREREG_v0.2.4_ACCEPTED_S2a.md` `5f5a7eaf538f3051adca384f0aaf231f93c218682401fc75be1a3566c8283c82`
  (all verified).
- `LeafEncodeV0` specification: `profile/LeafEncodeV0_SPEC.md` SHA-256
  `d142e636a9a92fdc57bbc49e77e077607ff12e96c19b79ad539b2f6b17b16008`;
  `LeafEncodeSpecArtifactDigestV0` `571765530870e4a6c028a54ec48aab8153411a15cfe30c44611c11c02925f9d5`
  (matches all 72 `pB` files and D2; L1–L5 leaf hashes recomputed by `scripts/s2a.py leafspec`).
- Toolchain: Lean (version 4.33.0, commit 5da8a13c67369827303c441170d2f4051339df4c, Release); `leanprover/lean4:v4.33.0`; conda-forge `lean4 4.33.0 build h6c1889d_0`;
  `lean` executable SHA-256 `9842f89b9a1874db969cc58933e4117c397338f795eb8febffeb79edd5272847`
  (identical to frozen S1's pin).
- S1: tag `v0.1.0-s1-ratified` (object `7c3df437…`, commit `e4db3747…`, git tree `6cdf48c2…`),
  vendored byte-for-byte; S1 verifier manifest `06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907`.
- `VerifierManifestS2aV0` SHA-256: `f8380b19b43334925e7f7621e1f7d7912f36c789199d3f8d069b87f5ea176d46`
- `VectorManifestS2aV0` SHA-256: `48ac65ff7ed0cbeabfcf6c8f781172fdcc9ab781e5bd3a361adf851a987a1d6e` (412 files)
- Partition check: passed (19 covered sources, 11 covered `.olean` files; no import of the test
  library; no manifest digest embedded in any covered file).

## Axiom audit (58 non-private theorems; permitted: propext, Classical.choice, Quot.sound)

    'P10S2.Codec.decNatAux_rep' depends on axioms: [propext, Quot.sound]
    'P10S2.Codec.decNatAux_inv' depends on axioms: [propext, Quot.sound]
    'P10S2.Codec.decListN_rt' depends on axioms: [propext]
    'P10S2.Codec.decListN_eq' depends on axioms: [propext, Quot.sound]
    'P10S2.Codec.decodeAll_enc' depends on axioms: [propext]
    'P10S2.Codec.enc_decodeAll' depends on axioms: [propext]
    'P10S2.s2_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.p10Verdict_halt' does not depend on any axioms
    'P10S2.p10Verdict_reject' does not depend on any axioms
    'P10S2.p10Verdict_some' depends on axioms: [propext]
    'P10S2.coverage_halt_no_verdict' depends on axioms: [propext, Quot.sound]
    'P10S2.unavailable_row_no_verdict' depends on axioms: [propext, Quot.sound]
    'P10S2.unavailable_payload_no_verdict' depends on axioms: [propext, Quot.sound]
    'P10S2.e2eCheck_of_parts' depends on axioms: [propext, Quot.sound]
    'P10S2.e2eCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.unavailable_key_no_verdict' depends on axioms: [propext, Quot.sound]
    'P10S2.missing_checkpoint_halts' depends on axioms: [propext, Quot.sound]
    'P10S2.e2eCheck_none_of_not_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.e2eCheck_halt_none' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.e2eCheck_reject_none' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.mem_idx_pairs' depends on axioms: [propext, Quot.sound]
    'P10S2.strictAscNat_pairwise' depends on axioms: [propext, Quot.sound]
    'P10S2.beforeAll_spec' depends on axioms: [propext, Quot.sound]
    'P10S2.finish_stage' depends on axioms: [propext]
    'P10S2.coreCheck_sound' depends on axioms: [propext, Quot.sound]
    'P10S2.coverage_sound' depends on axioms: [propext, Quot.sound]
    'P10S2.matchIdxs_mem' depends on axioms: [propext, Quot.sound]
    'P10S2.inj_on_of_nodup_map'' depends on axioms: [propext, Quot.sound]
    'P10S2.viewT_eq_subj' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.coverage_sound_view' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.fx_projection' does not depend on any axioms
    'P10S2.bundle_truth_nil' does not depend on any axioms
    'P10S2.bundle_truth_second' does not depend on any axioms
    'P10S2.bundle_truth_eU' does not depend on any axioms
    'P10S2.bundle_truth_eD' does not depend on any axioms
    'P10S2.bundle_truth_first_conflict' does not depend on any axioms
    'P10S2.bundle_truth_second_conflict' does not depend on any axioms
    'P10S2.bundle_truth_second_conflict_nofirst' does not depend on any axioms
    'P10S2.faithful_core' does not depend on any axioms
    'P10S2.mkEv_inE' does not depend on any axioms
    'P10S2.forall_mem_iff' depends on axioms: [propext, Quot.sound]
    'P10S2.bundle_faithful' depends on axioms: [propext, Quot.sound]
    'P10S2.fxBundle_of_mem_iff' depends on axioms: [propext]
    'P10S2.bundle_perm' depends on axioms: [propext]
    'P10S2.mem_eraseDups_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.bundle_dedup' depends on axioms: [propext, Classical.choice, Quot.sound]
    'P10S2.bundle_refines' depends on axioms: [propext, Quot.sound]
    'P10S2.readTok_append' depends on axioms: [propext]
    'P10S2.readTok_inv' depends on axioms: [propext, Quot.sound]
    'P10S2.tailEnc_len_pos' depends on axioms: [propext, Quot.sound]
    'P10S2.decTail_rt' depends on axioms: [propext, Quot.sound]
    'P10S2.decTail_eq' depends on axioms: [propext]
    'P10S2.entryC_first' depends on axioms: [propext, Quot.sound]
    'P10S2.elemC_first' depends on axioms: [propext, Quot.sound]
    'P10S2.decode_encode_profile' depends on axioms: [propext, Quot.sound]
    'P10S2.encode_decode_profile' depends on axioms: [propext, Quot.sound]
    'P10S2.decode_encode_transcript' depends on axioms: [propext, Quot.sound]
    'P10S2.encode_decode_transcript' depends on axioms: [propext, Quot.sound]

## Result matrix (each row = one kernel-checked theorem; TB7 column = harness result)

  id    prereg                                             cond          expected (Lean)                             tb7     status        
  D1    S2-D1                                              differential  equal                                       -       kernel-checked
  D2    G6-B3 (leaf spec artifact digest)                  differential  equal                                       -       kernel-checked
  K1    S2-K1 (K-1)                                        differential  equal                                       -       kernel-checked
  K2    S2-K2 (K-1)                                        differential  equal                                       -       kernel-checked
  K3    S2-K3 (K-1)                                        differential  equal                                       -       kernel-checked
  K4    S2-K4 (K-1)                                        differential  equal                                       -       kernel-checked
  K5    S2-K5 (K-1)                                        differential  equal                                       -       kernel-checked
  K6    S2-K6 (K-1)                                        differential  equal                                       -       kernel-checked
  K7    S2-K7 (K-1)                                        differential  equal                                       -       kernel-checked
  K8    S2-K8 (K-1)                                        differential  equal                                       -       kernel-checked
  N0    S2-N0                                              C9            .reject .c9_refsNotExactRelevantSet         -       kernel-checked
  N1    S2-N1                                              C9            .reject .c9_refsNotExactRelevantSet         -       kernel-checked
  N10   S2-N10                                             accept        .accept (.obs false none)                   -       kernel-checked
  N11   S2-N11                                             C1            .reject .c1_rowsNotContiguous               -       kernel-checked
  N12   S2-N12                                             C6            .halt .c6_noValidClosure                    -       kernel-checked
  N13a  S2-N13 (profile commitment absent)                 C3            .halt .c3_noProfileCommitment               -       kernel-checked
  N13b  S2-N13 (profile commitment after first admission)  C3            .reject .c3_profileAfterFirstAdmission      -       kernel-checked
  N14   S2-N14                                             C5            .reject .c5_citesNonOwnerLifecycle          -       kernel-checked
  N15   S2-N15                                             C8            .reject .c8_refNotRelevantAdmission         -       kernel-checked
  N16   S2-N16                                             C2            .halt .c2_rowUnavailable                    -       kernel-checked
  N17   S2-N17                                             C8            .reject .c8_refNotRelevantAdmission         -       kernel-checked
  N18   S2-N18                                             accept        .accept (.obs false none)                   -       kernel-checked
  N19   S2-N19                                             C1            .reject .c1_profileDigest                   -       kernel-checked
  N2    S2-N2                                              C7            .reject .c7_refsNotStrictlyAscending        -       kernel-checked
  N20   S2-N20                                             TB7           .accept (.obs false none)                   REJECT  kernel-checked
  N21   S2-N21                                             TB7           .accept (.obs false none)                   HALT    kernel-checked
  N22a  S2-N22 (fixture_id)                                C1            .reject .c1_profileFields                   -       kernel-checked
  N22b  S2-N22 (normative_profile_digest)                  C1            .reject .c1_profileFields                   -       kernel-checked
  N22c  S2-N22 (s1_profile_token)                          C1            .reject .c1_profileFields                   -       kernel-checked
  N23a  S2-N23 (extra field)                               C1            .reject .c1_profileDecode                   -       kernel-checked
  N23b  S2-N23 (missing field)                             C1            .reject .c1_profileDecode                   -       kernel-checked
  N23c  S2-N23 (non-canonical encoding)                    C1            .reject .c1_profileDecode                   -       kernel-checked
  N24   S2-N24 (B1)                                        C13           .reject .c13_closedEvidenceDigest           -       kernel-checked
  N25   S2-N25 (B1)                                        C13           .reject .c13_closedEvidenceDigest           -       kernel-checked
  N26   S2-N26 (B2)                                        C1a           .reject .c1a_ownerNotIssuer                 -       kernel-checked
  N27   S2-N27 (B2)                                        C1a           .reject .c1a_subjectDerivation              -       kernel-checked
  N28a  S2-N28a (B2,B4)                                    C1c           .reject .c1c_subjectDerivationDigest        -       kernel-checked
  N28b  S2-N28b (B4)                                       C1c           .reject .c1c_leafEncodingProfileDigest      -       kernel-checked
  N28c  S2-N28c (B4)                                       C1c           .reject .c1c_evidenceScopeDigest            -       kernel-checked
  N28d  S2-N28d (B4)                                       C1c           .reject .c1c_admissionRuleDigest            -       kernel-checked
  N28e  S2-N28e (B4)                                       C1c           .reject .c1c_coverageRuleDigest             -       kernel-checked
  N29   S2-N29 (B3)                                        C1b           .reject .c1b_admittersDigest                -       kernel-checked
  N3    S2-N3                                              C7            .reject .c7_refsNotStrictlyAscending        -       kernel-checked
  N30   S2-N30 (B3: key without authorization)             C8            .reject .c8_refNotRelevantAdmission         -       kernel-checked
  N31   S2-N31 (B3: authorization without key)             C2            .halt .c2_keyUnavailable                    -       kernel-checked
  N32a  S2-N32a (B5)                                       C11           .reject .c11_adjudicationRefsMismatch       -       kernel-checked
  N32b  S2-N32b (B5)                                       C11           .reject .c11_adjudicationRefsMismatch       -       kernel-checked
  N32c  S2-N32c (B5)                                       C11           .reject .c11_adjudicationRefsMismatch       -       kernel-checked
  N32d  S2-N32d (B5)                                       C11           .reject .c11_adjudicationRefsMismatch       -       kernel-checked
  N33   S2-N33 (B6: withdrawn raw-token claim digest)      E2E           .accept (.obs false none)                   -       kernel-checked
  N34   S2-N34 (I-2: legacy binary preclosure digest)      C6            .halt .c6_noValidClosure                    -       kernel-checked
  N35   S2-N35 (I-3: legacy binary key-resolution digest)  C1b           .reject .c1b_keyResolutionDigest            -       kernel-checked
  N36a  S2-N36a (G6-B1)                                    C3            .reject .c3_multipleProfileCommitments      -       kernel-checked
  N36b  S2-N36b (G6-B1)                                    C3            .reject .c3_multipleProfileCommitments      -       kernel-checked
  N36c  S2-N36c (G6-B1)                                    C3            .reject .c3_profileDigestMismatch           -       kernel-checked
  N4    S2-N4 (cited)                                      C8            .reject .c8_refNotRelevantAdmission         -       kernel-checked
  N4b   S2-N4 (uncited)                                    accept        .accept (.obs false none)                   -       kernel-checked
  N5    S2-N5                                              C10           .reject .c10_relevantAdmissionAfterClosure  -       kernel-checked
  N6a   S2-N6a                                             C4            .halt .c4_noInstanceCommitment              -       kernel-checked
  N6b   S2-N6b (two commitments)                           C4            .reject .c4_multipleCommitments             -       kernel-checked
  N6c   S2-N6b (conflicting commitment)                    C4            .reject .c4_multipleCommitments             -       kernel-checked
  N7a   S2-N7 (payload unavailable)                        C2            .halt .c2_subjectPayloadUnavailable         -       kernel-checked
  N7b   S2-N7 (checkpoint material missing)                TB5           .halt .tb5_checkpointMaterialUnavailable    -       kernel-checked
  N7c   S2-N7 (keyUnavailable, admitter)                   C2            .halt .c2_keyUnavailable                    -       kernel-checked
  N7d   S2-N7 (keyUnavailable, owner)                      C2            .halt .c2_keyUnavailable                    -       kernel-checked
  N8    S2-N8                                              C1            .reject .c1_logIdentity                     -       kernel-checked
  N9    S2-N9                                              C1b           .reject .c1b_keyResolutionDigest            -       kernel-checked
  P1    S2-P1                                              accept        .accept (.obs false (some false))           PASS    kernel-checked
  P2    S2-P2                                              accept        .accept (.obs false none)                   PASS    kernel-checked
  P2x   S2-P2 (literal scenario, no adjudication)          C11           .halt .c11_noAdjudicationAfterClosure       -       kernel-checked
  P3    S2-P3                                              accept        .accept P10.S1.Evidence.inconsistent        -       kernel-checked
  P3b   S2-P3 (closure [A1] only)                          C9            .reject .c9_refsNotExactRelevantSet         -       kernel-checked
  X1    addition                                           C1            .reject .c1b_admittersDigest                -       kernel-checked
  X10   addition (issuer outside the token alphabet)       C1a           .reject .c1a_issuerNotToken                 -       kernel-checked
  X2    addition (commitment differs from frozen inst)     C4            .reject .c4_commitmentMismatch              -       kernel-checked
  X3    addition (commitment after first admission)        C4            .reject .c4_commitmentAfterFirstAdmission   -       kernel-checked
  X4    addition (two valid closures)                      C6            .reject .c6_multipleClosures                -       kernel-checked
  X5    addition (empty closure)                           C12           .reject .c12_evidenceOutsideE               -       kernel-checked
  X6    addition (no closure)                              C6            .halt .c6_noValidClosure                    -       kernel-checked
  X7    addition (ref to an admission after the closure)   C9            .reject .c9_refsNotExactRelevantSet         -       kernel-checked
  X8    addition (adjudication not owner-signed)           C11           .halt .c11_noAdjudicationAfterClosure       -       kernel-checked
  X9    addition (owner listed in authorized_admitters)    C1b           .reject .c1_ownerInAdmitters                -       kernel-checked
matrix: 82 vectors (all preregistered P1-P3, P2x, N0-N36c, D1, K1-K8 present)

End-to-end: `V_P1_e2e`, `V_P2_e2e`, `V_N33_e2e` (each split over `V_<id>`, `V_<id>_dig`, `V_<id>_e2e`;
kernel-checked); must-fail: `N0_e2e`, `N11_e2e`, `no_hCov`, `no_hFaithful` (all rejected for the
expected reason).

Not covered by S2a (S2b, not authorized): execution of `LeafEncodeV0` (vectors L1–L8 in the spec are
normative examples; L1–L5 are recomputed by the harness, not executed by Lean), recomputation of
`LogIdentityV0`, and `TranscriptFaithful`.

See `IMPLEMENTATION_BINDING.md` for every interpretation, including those superseded by prereg
v0.2.5/v0.2.6.
