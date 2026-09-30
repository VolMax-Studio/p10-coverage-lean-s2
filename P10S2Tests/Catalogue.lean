import P10S2Tests.Model

/-!
# P10S2Tests.Catalogue — every vector of prereg §11 (P1–P3, N0–N23) plus a few additions

Each entry is the scenario AND its preregistered expected outcome, written by hand from the
prereg table. The generator turns entries into byte files and Lean test modules; the Lean tests
then check the checker against these expectations using the kernel.
-/

namespace P10S2Tests
open P10S2 P10.Sha256

structure VectorSpec where
  id      : String
  prereg  : String
  cond    : String
  pB      : Bytes
  inst    : InstanceCommitment
  T       : Option (Transcript FxItem)
  /-- Lean text of the expected `Option (CoverageOutcome _)` right-hand side. -/
  expect  : String
  /-- TB7 harness expectation for this vector's `pB` (`PASS` / `REJECT` / `HALT`), if any. -/
  tb7     : Option String := none
  /-- S1 instance bytes, when the vector is composed with S1. -/
  iB      : Option Bytes := none
  /-- Lean text of the expected `runE2E` result, when composed. -/
  e2e     : Option String := none
  extra   : String := ""
  note    : String := ""

def replaceFirst (needle rep : Bytes) : Bytes → Bytes
  | [] => []
  | x :: xs =>
    if needle.isPrefixOf (x :: xs) then rep ++ (x :: xs).drop needle.length
    else x :: replaceFirst needle rep xs

def s1Bytes (c : P10.S1.Claim) (e : P10.S1.Evidence) (w0 w1 : P10.S1.World) : Bytes :=
  P10.Wire.encode ⟨c, e, w0, w1⟩

def catalogue (md : Tok) : List VectorSpec :=
  let pB := encodeProfileArtifact (profileOf md)
  let inst := instOf pB
  let ok (id prereg cond : String) (leaves : List Leaf) (expect : String) : VectorSpec :=
    { id, prereg, cond, pB, inst, T := some (tOf inst leaves), expect }
  let eUb := s1Bytes .secondBit (.obs false none) .w00 .w01
  let eDb := s1Bytes .secondBit (.obs false (some false)) .w00 .w01
  let eUexp := ".accept (.obs false none)"
  -- pB variants (commitment re-digested so that only the pB property differs)
  let withPB (id prereg cond : String) (pBv : Bytes) (expect : String) (tb7 : Option String) :
      VectorSpec :=
    let instv := instOf pBv
    { id, prereg, cond, pB := pBv, inst := instv, T := some (tOf instv (standard instv [a1] [2])),
      expect, tb7 }
  let altMd := mkTok (bytes% "0000000000000000000000000000000000000000000000000000000000000000")
  [
  -- ===== positive controls =====
  { ok "P1" "S2-P1" "accept" (standard inst [a1, a2] [2, 3])
      ".accept (.obs false (some false))" with
    iB := some eDb, e2e := some "none", tb7 := some "PASS",
    extra := "theorem s1_determinate : P10.Determinate P10.S1.profile (P10.S1.Evidence.obs false (some false)) P10.S1.Claim.secondBit :=\n  P10.S1.none_does_not_decide_determinacy.2.2.1\ntheorem s1_no_certificate : ¬ Nonempty (P10.UnderdeterminationCertificate P10.S1.profile (P10.S1.Evidence.obs false (some false)) P10.S1.Claim.secondBit) :=\n  P10.S1.n1_determined_no_certificate\n",
    note := "bundle [A1,A2] = eD; S1 finds Determinate, so no S1 certificate; e2e = none" },
  { ok "P2" "S2-P2" "accept" (standard inst [a1] [2]) eUexp with
    iB := some eUb, e2e := some "some (.obs false none, .secondBit)", tb7 := some "PASS",
    extra := "theorem chain :\n    ∃ T : Transcript fx.Item, decodeTranscript fxItemC tB = some T ∧\n      (∀ V : LogView fx.Item, TranscriptFaithful T V →\n        CoverageSpecV fx inst pB V (P10.S1.Evidence.obs false none)) ∧\n      P10.Underdetermined P10.S1.profile (P10.S1.Evidence.obs false none) P10.S1.Claim.secondBit := by\n  have hI : decodeInst instB = some inst := (Option.some_get _).symm\n  have h : e2eCheck tDigest tB pB iB inst = some (P10.S1.Evidence.obs false none, P10.S1.Claim.secondBit) := by\n    have h0 := e2e_outcome\n    unfold runE2E at h0\n    rw [hI] at h0\n    simpa using h0\n  obtain ⟨_, T, hT, _, _, _, _, hu, hv⟩ := e2eCheck_sound h\n  exact ⟨T, hT, hv, hu⟩\n",
    note := "composes with S1 under §9" },
  { ok "P2x" "S2-P2 (literal scenario, no adjudication)" "C11"
      ([lf_pc inst, lf_ic inst, a1] ++ [lf_closure inst [lf_pc inst, lf_ic inst, a1] [2]])
      ".halt .c11_noAdjudicationAfterClosure" with
    note := "PREREG CONFLICT: P2 lists no adjudication but C11 requires one; see README" },
  { ok "P3" "S2-P3" "accept" (standard inst [a1, a3] [2, 3])
      ".accept P10.S1.Evidence.inconsistent" with
    extra := "theorem s1_cannot_certify : ¬ Nonempty (P10.UnderdeterminationCertificate P10.S1.profile P10.S1.Evidence.inconsistent P10.S1.Claim.secondBit) :=\n  P10.S1.n4_no_certificate_not_determinate.1\n",
    note := "masking control: conflicting admissions accepted as `inconsistent`; S1 cannot certify" },
  ok "P3b" "S2-P3 (closure [A1] only)" "C9" (standard inst [a1, a3] [2])
    ".reject .c9_refsNotExactRelevantSet",
  -- ===== negatives =====
  { ok "N0" "S2-N0" "C9" (standard inst [a1, a2] [2]) ".reject .c9_refsNotExactRelevantSet" with
    iB := some eUb,
    note := "strategic omission; E2E must-fail in P10S2TestsMustFail" },
  ok "N1" "S2-N1" "C9" (standard inst [a1, a2, a2'] [2, 4]) ".reject .c9_refsNotExactRelevantSet",
  ok "N2" "S2-N2" "C7" (standard inst [a1, a2] [2, 2]) ".reject .c7_refsNotStrictlyAscending",
  ok "N3" "S2-N3" "C7" (standard inst [a1, a2] [3, 2]) ".reject .c7_refsNotStrictlyAscending",
  ok "N4" "S2-N4 (cited)" "C8"
    (standard inst [a1, adm intruder (.second false)] [2, 3])
    ".reject .c8_refNotRelevantAdmission",
  ok "N4b" "S2-N4 (uncited)" "accept"
    (standard inst [a1, adm intruder (.second false)] [2]) eUexp,
  ok "N5" "S2-N5" "C10"
    (let pre := [lf_pc inst, lf_ic inst, a1]
     pre ++ [lf_closure inst pre [2], a2, lf_adj 0 1 pre.length])
    ".reject .c10_relevantAdmissionAfterClosure",
  ok "N6a" "S2-N6a" "C4" (withClosure inst [lf_pc inst, a1] [1])
    ".halt .c4_noInstanceCommitment",
  ok "N6b" "S2-N6b (two commitments)" "C4" (standard inst [lf_ic inst, a1] [3])
    ".reject .c4_multipleCommitments",
  ok "N6c" "S2-N6b (conflicting commitment)" "C4"
    (standard inst
      [.e ownerIss .instanceCommit .verified
        (some (.instanceCommit { inst with claimDigest := claimDigest .firstBit })), a1] [3])
    ".reject .c4_multipleCommitments",
  ok "N7a" "S2-N7 (payload unavailable)" "C2"
    (standard inst [.e adm1 .admission .verified none] [2])
    ".halt .c2_subjectPayloadUnavailable",
  { id := "N7b", prereg := "S2-N7 (checkpoint material missing)", cond := "TB5", pB, inst,
    T := none, expect := ".halt .tb5_checkpointMaterialUnavailable" },
  ok "N7c" "S2-N7 (keyUnavailable, admitter)" "C2"
    (standard inst [.e adm1 .admission .keyUnavailable (some (.admission (.first false)))] [2])
    ".halt .c2_keyUnavailable",
  ok "N7d" "S2-N7 (keyUnavailable, owner)" "C2"
    (standard inst [a1, .e ownerIss .profileCommit .keyUnavailable
        (some (.profileCommit inst.profileDigest))] [2])
    ".halt .c2_keyUnavailable",
  { id := "N8", prereg := "S2-N8", cond := "C1", pB, inst
    T := some { tOf inst (standard inst [a1] [2]) with
      logIdentityDigest := ⟨bytes% "some-other-log"⟩ }
    expect := ".reject .c1_logIdentity" },
  { id := "N9", prereg := "S2-N9", cond := "C1", pB := encodeProfileArtifact (profileOf md keyResAlt),
    inst := instOf (encodeProfileArtifact (profileOf md keyResAlt))
    T := some (tOf inst (standard inst [a1] [2]))
    expect := ".reject .c1_keyResolutionDigest",
    note := "same transcript, different key mapping; commitment re-digested" },
  ok "N10" "S2-N10" "accept"
    (withClosure inst [lf_pc inst, lf_ic inst, a1, .other siblingSub, .other siblingSub] [2]) eUexp,
  { id := "N11", prereg := "S2-N11", cond := "C1", pB, inst,
    T := some (buildT inst krDigestOf
      ([lf_pc inst, lf_ic inst, a1] ++ [lf_closure inst [lf_pc inst, lf_ic inst, a1] [2]]) 6)
    expect := ".reject .c1_rowsNotContiguous", iB := some eUb,
    note := "rows stop at the closure leaf; checkpoint.size = 6; E2E must-fail" },
  ok "N12" "S2-N12" "C6"
    (let pre := [lf_pc inst, lf_ic inst, a1, a2]
     pre ++ [lf_closure inst [lf_pc inst, lf_ic inst, a1] [2], lf_adj 0 1 pre.length])
    ".halt .c6_noValidClosure",
  ok "N13a" "S2-N13 (profile commitment absent)" "C3"
    (withClosure inst [lf_ic inst, a1] [1]) ".halt .c3_noProfileCommitment",
  ok "N13b" "S2-N13 (profile commitment after first admission)" "C3"
    (withClosure inst [lf_ic inst, a1, lf_pc inst] [1])
    ".reject .c3_profileAfterFirstAdmission",
  ok "N14" "S2-N14" "C5"
    (let pre := [lf_pc inst, lf_ic inst, a1]
     pre ++ [lf_closure inst pre [2],
       .e adm1 .closure .verified
         (some (.closure ⟨inst.instanceSubject, true, [2], closedDigest, digestBefore inst pre⟩)),
       lf_adj 0 1 4])
    ".reject .c5_citesNonOwnerLifecycle",
  ok "N15" "S2-N15" "C8"
    (standard inst [a1, .e adm1 .admission .badSignature (some (.admission (.second false)))] [2, 3])
    ".reject .c8_refNotRelevantAdmission",
  ok "N16" "S2-N16" "C2"
    (withClosure inst [lf_pc inst, lf_ic inst, .unavail, a1] [3])
    ".halt .c2_rowUnavailable",
  ok "N17" "S2-N17" "C8"
    (standard inst [a1, .other subjOffByOne] [2, 3]) ".reject .c8_refNotRelevantAdmission",
  ok "N18" "S2-N18" "accept"
    (standard inst [a1, .e intruder .admission .keyUnavailable (some (.admission (.second false)))] [2])
    eUexp,
  { id := "N19", prereg := "S2-N19", cond := "C1", pB,
    inst := { inst with profileDigest := ⟨bytes% "not-the-digest-of-pB"⟩ },
    T := some (tOf inst (standard inst [a1] [2]))
    expect := ".reject .c1_profileDigest" },
  { withPB "N20" "S2-N20" "TB7" (encodeProfileArtifact (profileOf altMd)) eUexp (some "REJECT") with
    note := "Lean accepts (manifest identity is not a Lean fact); the TB7 harness REJECTs" },
  { withPB "N21" "S2-N21" "TB7"
      (encodeProfileArtifact (profileOf md (mref := mkTok (bytes% "MissingManifest.json")))) eUexp
      (some "HALT") with
    note := "Lean accepts; the TB7 harness HALTs (manifest ref does not resolve)" },
  withPB "N22a" "S2-N22 (fixture_id)" "C1"
    (encodeProfileArtifact (profileOf md (fixtureId := mkTok (bytes% "other-fixture-v9"))))
    ".reject .c1_profileFields" none,
  withPB "N22b" "S2-N22 (normative_profile_digest)" "C1"
    (encodeProfileArtifact (profileOf md (spec := mkTok (bytes% "sha256:0000"))))
    ".reject .c1_profileFields" none,
  withPB "N22c" "S2-N22 (s1_profile_token)" "C1"
    (encodeProfileArtifact (profileOf md (s1tok := mkTok (bytes% "p10-s1-other-v0"))))
    ".reject .c1_profileFields" none,
  withPB "N23a" "S2-N23 (extra field)" "C1"
    (replaceFirst (bytes% "{\"admission") (bytes% "{\"extra\":\"x\",\"admission") pB)
    ".reject .c1_profileDecode" none,
  withPB "N23b" "S2-N23 (missing field)" "C1"
    (replaceFirst (bytes% ",\"coverage_rule_id\":\"coverage-rules-v0\"") [] pB)
    ".reject .c1_profileDecode" none,
  withPB "N23c" "S2-N23 (non-canonical encoding)" "C1"
    (replaceFirst (bytes% "\"fixture_id\":\"") (bytes% "\"fixture_id\": \"") pB)
    ".reject .c1_profileDecode" none,
  -- ===== additions (not in the prereg table) =====
  { id := "X1", prereg := "addition", cond := "C1", pB,
    inst := { inst with authorizedAdmitterSetDigest := ⟨bytes% "wrong-admitter-set"⟩ },
    T := some (tOf inst (standard inst [a1] [2])), expect := ".reject .c1_admitterSetDigest" },
  ok "X2" "addition (commitment differs from frozen inst)" "C4"
    (withClosure inst [lf_pc inst,
      .e ownerIss .instanceCommit .verified
        (some (.instanceCommit { inst with evidenceScopeDigest := ⟨bytes% "other-scope"⟩ })), a1] [2])
    ".reject .c4_commitmentMismatch",
  ok "X3" "addition (commitment after first admission)" "C4"
    (withClosure inst [lf_pc inst, a1, lf_ic inst] [1])
    ".reject .c4_commitmentAfterFirstAdmission",
  ok "X4" "addition (two valid closures)" "C6"
    (let pre := [lf_pc inst, lf_ic inst, a1]
     let cl1 := lf_closure inst pre [2]
     let pre2 := pre ++ [cl1]
     pre2 ++ [lf_closure inst pre2 [2], lf_adj 0 1 pre.length])
    ".reject .c6_multipleClosures",
  ok "X5" "addition (empty closure)" "C12"
    (standard inst [] []) ".reject .c12_evidenceOutsideE",
  ok "X6" "addition (no closure)" "C6"
    [lf_pc inst, lf_ic inst, a1, lf_adj 0 1 2] ".halt .c6_noValidClosure",
  ok "X7" "addition (ref to an admission after the closure)" "C9"
    (let pre := [lf_pc inst, lf_ic inst, a1]
     pre ++ [lf_closure inst pre [2, 4], a2, lf_adj 0 1 pre.length])
    ".reject .c9_refsNotExactRelevantSet",
  ok "X8" "addition (adjudication not owner-signed)" "C11"
    (let pre := [lf_pc inst, lf_ic inst, a1]
     pre ++ [lf_closure inst pre [2],
       .e adm1 .adjudication .verified (some (.adjudication 0 1 3))])
    ".halt .c11_noAdjudicationAfterClosure"
  ]

end P10S2Tests
