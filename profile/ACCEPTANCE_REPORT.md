# S2a acceptance report (implementation checks; NOT a gate verdict, NOT ratification)

Recorded by running `P10_ALLOW_INTREE_PIN=1 ./scripts/verify.sh` at implementation commit
`15589cf2d92c83593c66ff1cc16210e7da37b841` (exit 0). In-tree pins prove self-consistency only;
the canonical run takes both pins out of band.

- Preregistration: `S2_PREREG_v0.2.4_ACCEPTED_S2a.md`, SHA-256
  `5f5a7eaf538f3051adca384f0aaf231f93c218682401fc75be1a3566c8283c82` (verified).
- Toolchain: Lean (version 4.33.0, commit 5da8a13c67369827303c441170d2f4051339df4c, Release); `leanprover/lean4:v4.33.0`; conda-forge `lean4 4.33.0 build h6c1889d_0`;
  `lean` executable SHA-256 `9842f89b9a1874db969cc58933e4117c397338f795eb8febffeb79edd5272847`
  (identical to frozen S1's pin).
- S1: tag `v0.1.0-s1-ratified` (object `7c3df437…`, commit `e4db3747…`, git tree `6cdf48c2…`),
  vendored byte-for-byte; S1 verifier manifest `06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907`.
- `VerifierManifestS2aV0` SHA-256: `c348a35f4d69226a9c2ca6c7d8dbfd23c30c912e572d255ee27b55c79089ef61`
- `VectorManifestS2aV0` SHA-256: `3d78e09cec628e19ad0164653d173c115bcbb63ee258d7d18fcc7cb817953633`
- Partition check: passed (17 covered sources, 10 covered `.olean` files; no import of the test
  library; no manifest digest embedded in any covered file).

## Axiom audit (56 non-private theorems; permitted: propext, Classical.choice, Quot.sound)

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
    'P10S2.decode_encode_profile' depends on axioms: [propext, Quot.sound]
    'P10S2.encode_decode_profile' depends on axioms: [propext, Quot.sound]
    'P10S2.decode_encode_transcript' depends on axioms: [propext, Quot.sound]
    'P10S2.encode_decode_transcript' depends on axioms: [propext, Quot.sound]

## Result matrix (each row = one kernel-checked theorem; TB7 column = harness result)

      id    prereg                                             cond    expected (Lean)                             tb7     status        
      N0    S2-N0                                              C9      .reject .c9_refsNotExactRelevantSet         -       kernel-checked
      N1    S2-N1                                              C9      .reject .c9_refsNotExactRelevantSet         -       kernel-checked
      N10   S2-N10                                             accept  .accept (.obs false none)                   -       kernel-checked
      N11   S2-N11                                             C1      .reject .c1_rowsNotContiguous               -       kernel-checked
      N12   S2-N12                                             C6      .halt .c6_noValidClosure                    -       kernel-checked
      N13a  S2-N13 (profile commitment absent)                 C3      .halt .c3_noProfileCommitment               -       kernel-checked
      N13b  S2-N13 (profile commitment after first admission)  C3      .reject .c3_profileAfterFirstAdmission      -       kernel-checked
      N14   S2-N14                                             C5      .reject .c5_citesNonOwnerLifecycle          -       kernel-checked
      N15   S2-N15                                             C8      .reject .c8_refNotRelevantAdmission         -       kernel-checked
      N16   S2-N16                                             C2      .halt .c2_rowUnavailable                    -       kernel-checked
      N17   S2-N17                                             C8      .reject .c8_refNotRelevantAdmission         -       kernel-checked
      N18   S2-N18                                             accept  .accept (.obs false none)                   -       kernel-checked
      N19   S2-N19                                             C1      .reject .c1_profileDigest                   -       kernel-checked
      N2    S2-N2                                              C7      .reject .c7_refsNotStrictlyAscending        -       kernel-checked
      N20   S2-N20                                             TB7     .accept (.obs false none)                   REJECT  kernel-checked
      N21   S2-N21                                             TB7     .accept (.obs false none)                   HALT    kernel-checked
      N22a  S2-N22 (fixture_id)                                C1      .reject .c1_profileFields                   -       kernel-checked
      N22b  S2-N22 (normative_profile_digest)                  C1      .reject .c1_profileFields                   -       kernel-checked
      N22c  S2-N22 (s1_profile_token)                          C1      .reject .c1_profileFields                   -       kernel-checked
      N23a  S2-N23 (extra field)                               C1      .reject .c1_profileDecode                   -       kernel-checked
      N23b  S2-N23 (missing field)                             C1      .reject .c1_profileDecode                   -       kernel-checked
      N23c  S2-N23 (non-canonical encoding)                    C1      .reject .c1_profileDecode                   -       kernel-checked
      N3    S2-N3                                              C7      .reject .c7_refsNotStrictlyAscending        -       kernel-checked
      N4    S2-N4 (cited)                                      C8      .reject .c8_refNotRelevantAdmission         -       kernel-checked
      N4b   S2-N4 (uncited)                                    accept  .accept (.obs false none)                   -       kernel-checked
      N5    S2-N5                                              C10     .reject .c10_relevantAdmissionAfterClosure  -       kernel-checked
      N6a   S2-N6a                                             C4      .halt .c4_noInstanceCommitment              -       kernel-checked
      N6b   S2-N6b (two commitments)                           C4      .reject .c4_multipleCommitments             -       kernel-checked
      N6c   S2-N6b (conflicting commitment)                    C4      .reject .c4_multipleCommitments             -       kernel-checked
      N7a   S2-N7 (payload unavailable)                        C2      .halt .c2_subjectPayloadUnavailable         -       kernel-checked
      N7b   S2-N7 (checkpoint material missing)                TB5     .halt .tb5_checkpointMaterialUnavailable    -       kernel-checked
      N7c   S2-N7 (keyUnavailable, admitter)                   C2      .halt .c2_keyUnavailable                    -       kernel-checked
      N7d   S2-N7 (keyUnavailable, owner)                      C2      .halt .c2_keyUnavailable                    -       kernel-checked
      N8    S2-N8                                              C1      .reject .c1_logIdentity                     -       kernel-checked
      N9    S2-N9                                              C1      .reject .c1_keyResolutionDigest             -       kernel-checked
      P1    S2-P1                                              accept  .accept (.obs false (some false))           PASS    kernel-checked
      P2    S2-P2                                              accept  .accept (.obs false none)                   PASS    kernel-checked
      P2x   S2-P2 (literal scenario, no adjudication)          C11     .halt .c11_noAdjudicationAfterClosure       -       kernel-checked
      P3    S2-P3                                              accept  .accept P10.S1.Evidence.inconsistent        -       kernel-checked
      P3b   S2-P3 (closure [A1] only)                          C9      .reject .c9_refsNotExactRelevantSet         -       kernel-checked
      X1    addition                                           C1      .reject .c1_admitterSetDigest               -       kernel-checked
      X2    addition (commitment differs from frozen inst)     C4      .reject .c4_commitmentMismatch              -       kernel-checked
      X3    addition (commitment after first admission)        C4      .reject .c4_commitmentAfterFirstAdmission   -       kernel-checked
      X4    addition (two valid closures)                      C6      .reject .c6_multipleClosures                -       kernel-checked
      X5    addition (empty closure)                           C12     .reject .c12_evidenceOutsideE               -       kernel-checked
      X6    addition (no closure)                              C6      .halt .c6_noValidClosure                    -       kernel-checked
      X7    addition (ref to an admission after the closure)   C9      .reject .c9_refsNotExactRelevantSet         -       kernel-checked
      X8    addition (adjudication not owner-signed)           C11     .halt .c11_noAdjudicationAfterClosure       -       kernel-checked
    matrix: 48 vectors (all preregistered P1-P3, N0-N23 present)
    

End-to-end: `V_P1_e2e`, `V_P2_e2e` (kernel-checked); must-fail: `N0_e2e`, `N11_e2e`,
`no_hCov`, `no_hFaithful` (all rejected for the expected reason).

See `IMPLEMENTATION_BINDING.md` for every interpretation and the S2-P2/C11 conflict (I-1).
