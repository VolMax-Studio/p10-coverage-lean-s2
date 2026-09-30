import P10S2.CoverageSpec
import P10.Bound

/-!
# P10S2.Composition — the byte-level S2 → S1 chain (prereg §9, §10)

```text
complete closure refs
  → canonical Bundle(refs)                              (coverageCheck, C9, C12)
  → evidence e
  → e = evidence decoded from the S1 instance bytes iB  (hEv, computed by `e2eCheck`)
  → P10.Bound iB (sha256 iB)                            (S1, unchanged)
  → CertificateTargetV0 → Underdetermined P10.S1.profile e c
```

Nothing is shared only as an abstract variable `e`: `s2_end_to_end` ties the evidence that
coverage accepted to the evidence *decoded from the S1 bytes*, and `e2eCheck` computes those
equalities from the committed bytes instead of taking them as assumptions (S1's M34 pattern).
`hCov` and `hFaithful` are both needed for the `CoverageSpecV` conjunct.

Profile identity is NOT extracted from `iB` (S1 bytes do not carry it). The chain is
`InstanceCommitment.profile_digest = sha256 pB` (checked in C1) → decoded `pB` →
`verifier_manifest_digest` → TB7 acceptance harness (outside Lean).
-/

namespace P10S2
open P10.Sha256 (sha256)

/-- Canonical codec of the fixture's admission items (used by the transcript codec). -/
def fxItemC : Codec FxItem :=
  Codec.iso (Codec.sum Codec.bool Codec.bool)
    (fun i => match i with | .first b => Sum.inl b | .second b => Sum.inr b)
    (fun s => match s with | Sum.inl b => .first b | Sum.inr b => .second b)
    (by intro a; cases a <;> rfl)
    (by intro b; rcases b with b | b <;> rfl)

/-- Digest of the S1 canonical claim token bytes (prereg §6a). -/
def claimDigest (c : P10.S1.Claim) : Digest := ⟨sha256 (P10.Wire.claimTok c)⟩

/-- **`s2_end_to_end`** (prereg §9). -/
theorem s2_end_to_end
    {tB pB iB : Bytes} {inst : InstanceCommitment} {T : Transcript fx.Item}
    {V : LogView fx.Item} {prof : ProfileArtifact} {si : P10.Wire.Instance}
    {c : P10.S1.Claim} {e : P10.S1.Evidence}
    (hT : decodeTranscript fxItemC tB = some T)
    (hPB : decodeProfileArtifact pB = some prof)
    (hFaithful : TranscriptFaithful T V)
    (hCov : coverageCheck fx inst pB T = .accept e)
    (hS1 : P10.Bound iB (sha256 iB))
    (hDec : P10.Wire.decode iB = some si)
    (hEv : si.evidence = e)
    (hC : si.claim = c ∧ claimDigest c = inst.claimDigest) :
    CoverageSpecV fx inst pB V e ∧ encodeTranscript fxItemC T = tB ∧
    inst.profileDigest.bytes = sha256 pB ∧ prof.fixtureId.1 = fx.fixtureId ∧
    P10.Underdetermined P10.S1.profile e c := by
  have hview := coverage_sound_view fx inst pB T V e hFaithful hCov
  have hs := coverage_sound fx inst pB T e hCov
  refine ⟨hview, encode_decode_transcript fxItemC tB T hT, hs.profileDigest.symm, ?_, ?_⟩
  · obtain ⟨prof', hp', hfx, _⟩ := hs.profile
    rw [hPB] at hp'
    have : prof = prof' := Option.some.inj hp'
    subst this
    exact hfx
  · have hu := P10.Wire.holds_underdetermined hDec hS1.holds
    rw [hEv, hC.1] at hu
    exact hu

/-! ### Verdicts: HALT and REJECT never produce an epistemic verdict -/

inductive P10Verdict
  | notDemonstratedUnderdetermined

/-- The composed verdict function. `s1Certifies e` is the S1 side of the composition. -/
def p10Verdict {E : Type} (s1Certifies : E → Bool) : CoverageOutcome E → Option P10Verdict
  | .accept e => if s1Certifies e = true then some .notDemonstratedUnderdetermined else none
  | .reject _ => none
  | .halt _ => none

theorem p10Verdict_halt {E : Type} (s : E → Bool) (r : HaltReason) :
    p10Verdict s (.halt r) = none := rfl

theorem p10Verdict_reject {E : Type} (s : E → Bool) (r : RejectReason) :
    p10Verdict s (.reject r) = none := rfl

theorem p10Verdict_some {E : Type} {s : E → Bool} {o : CoverageOutcome E} {v : P10Verdict}
    (h : p10Verdict s o = some v) : ∃ e, o = .accept e ∧ s e = true := by
  cases o with
  | accept e =>
    refine ⟨e, rfl, ?_⟩
    simp only [p10Verdict] at h
    by_cases hs : s e = true
    · exact hs
    · simp [hs] at h
  | reject r => simp [p10Verdict] at h
  | halt r => simp [p10Verdict] at h

/-- Any HALT of `coverageCheck` yields no verdict, through the composed function. -/
theorem coverage_halt_no_verdict (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Transcript π.Item) (s : π.Evidence → Bool) (r : HaltReason)
    (h : coverageCheck π inst pB T = .halt r) : p10Verdict s (coverageCheck π inst pB T) = none := by
  rw [h]; rfl

/-- A transcript with an unavailable row never reaches `accept`, hence never a verdict. -/
theorem unavailable_row_no_verdict (π : AdmissionProfile) (inst : InstanceCommitment)
    (pB : Bytes) (T : Transcript π.Item) (s : π.Evidence → Bool)
    (hu : ∃ r ∈ T.rows, rowUnavailable r = true) :
    p10Verdict s (coverageCheck π inst pB T) = none := by
  cases hv : p10Verdict s (coverageCheck π inst pB T) with
  | none => rfl
  | some v =>
    obtain ⟨e, he, _⟩ := p10Verdict_some hv
    have hsnd := coverage_sound π inst pB T e he
    obtain ⟨r, hr, hru⟩ := hu
    have := hsnd.noUnavailableRow r hr
    rw [hru] at this
    exact absurd this (by decide)

/-- A subject entry whose payload is not obtainable never reaches a verdict. -/
theorem unavailable_payload_no_verdict (π : AdmissionProfile) (inst : InstanceCommitment)
    (pB : Bytes) (T : Transcript π.Item) (s : π.Evidence → Bool)
    (hu : ∃ d ∈ T.detailed, d.payload = none) :
    p10Verdict s (coverageCheck π inst pB T) = none := by
  cases hv : p10Verdict s (coverageCheck π inst pB T) with
  | none => rfl
  | some v =>
    obtain ⟨e, he, _⟩ := p10Verdict_some hv
    have hsnd := coverage_sound π inst pB T e he
    obtain ⟨d, hd, hdn⟩ := hu
    have := hsnd.payloadsAvailable d hd
    rw [hdn] at this
    simp at this

/-! ### The checker-owned end-to-end statement -/

/-- Computes every link from the committed bytes: `tB` (bound to `tDigest`), `pB`, `iB`. -/
def e2eCheck (tDigest tB pB iB : Bytes) (inst : InstanceCommitment) :
    Option (P10.S1.Evidence × P10.S1.Claim) :=
  if sha256 tB = tDigest then
    match decodeTranscript fxItemC tB with
    | none => none
    | some T =>
      match coverageCheck fx inst pB T with
      | .accept e =>
        match P10.Wire.decode iB with
        | none => none
        | some si =>
          let e' : P10.S1.Evidence := e
          if decide (si.evidence = e') && decide (claimDigest si.claim = inst.claimDigest) &&
              P10.Wire.check iB then some (e', si.claim) else none
      | .reject _ => none
      | .halt _ => none
  else none

/-- **Checker-owned proposition**: `hEv`, `hC`, the S1 statement and the transcript digest are all
established by computation; only `TranscriptFaithful` (TB2) remains a premise. -/
theorem e2eCheck_sound {tDigest tB pB iB : Bytes} {inst : InstanceCommitment}
    {e : P10.S1.Evidence} {c : P10.S1.Claim}
    (h : e2eCheck tDigest tB pB iB inst = some (e, c)) :
    sha256 tB = tDigest ∧
    ∃ (T : Transcript fx.Item), decodeTranscript fxItemC tB = some T ∧
      encodeTranscript fxItemC T = tB ∧
      coverageCheck fx inst pB T = .accept e ∧
      claimDigest c = inst.claimDigest ∧
      P10.Bound iB (sha256 iB) ∧
      P10.Underdetermined P10.S1.profile e c ∧
      ∀ V : LogView fx.Item, TranscriptFaithful T V → CoverageSpecV fx inst pB V e := by
  unfold e2eCheck at h
  split at h
  · rename_i hd
    refine ⟨hd, ?_⟩
    split at h
    · simp at h
    · rename_i T hT
      split at h
      · rename_i e' hc
        split at h
        · simp at h
        · rename_i si hdec
          simp only [] at h
          split at h
          · rename_i hb
            have hp := Option.some.inj h
            have he : e' = e := congrArg Prod.fst hp
            have hcl : si.claim = c := congrArg Prod.snd hp
            subst he; subst hcl
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
            obtain ⟨⟨hev, hcd⟩, hchk⟩ := hb
            have hholds := P10.Wire.holds_of_check hchk
            have hu := P10.Wire.holds_underdetermined hdec hholds
            rw [hev] at hu
            exact ⟨T, hT, encode_decode_transcript fxItemC tB T hT, hc, hcd,
              ⟨rfl, hholds⟩, hu, fun V hf => coverage_sound_view fx inst pB T V _ hf hc⟩
          · simp at h
      · simp at h
      · simp at h
  · simp at h

/-- An authorized (owner or admitter) entry whose key is unavailable never reaches a verdict. -/
theorem unavailable_key_no_verdict (π : AdmissionProfile) (inst : InstanceCommitment)
    (pB : Bytes) (T : Transcript π.Item) (s : π.Evidence → Bool) (prof : ProfileArtifact)
    (hp : decodeProfileArtifact pB = some prof)
    (hu : ∃ d ∈ T.detailed,
      authorizedIss ⟨π.admissible, inst, admittersOf inst.instanceOwnerIss prof.keyResolution⟩
        d.iss = true ∧ d.sig = .keyUnavailable) :
    p10Verdict s (coverageCheck π inst pB T) = none := by
  cases hv : p10Verdict s (coverageCheck π inst pB T) with
  | none => rfl
  | some v =>
    obtain ⟨e, he, _⟩ := p10Verdict_some hv
    have hsnd := coverage_sound π inst pB T e he
    obtain ⟨prof', hp', _, _, _, _, _, hkeys, _⟩ := hsnd.profile
    rw [hp] at hp'
    have hpp : prof = prof' := Option.some.inj hp'
    subst hpp
    obtain ⟨d, hd, hauth, hsig⟩ := hu
    exact absurd hsig (hkeys d hd hauth)

/-- Missing checkpoint material (TB5): HALT, and no verdict. -/
theorem missing_checkpoint_halts (π : AdmissionProfile) (inst : InstanceCommitment)
    (pB : Bytes) (s : π.Evidence → Bool) :
    coverageCheckM π inst pB none = .halt .tb5_checkpointMaterialUnavailable ∧
    p10Verdict s (coverageCheckM π inst pB none) = none := ⟨rfl, rfl⟩

/-- The composed end-to-end checker yields no result when coverage HALTs or REJECTs:
HALT never yields an epistemic verdict, through the function that actually composes S2 and S1. -/
theorem e2eCheck_none_of_not_accept {tDigest tB pB iB : Bytes} {inst : InstanceCommitment}
    {T : Transcript fx.Item} (hT : decodeTranscript fxItemC tB = some T)
    (hna : ∀ e, coverageCheck fx inst pB T ≠ .accept e) :
    e2eCheck tDigest tB pB iB inst = none := by
  cases h : e2eCheck tDigest tB pB iB inst with
  | none => rfl
  | some ec =>
    obtain ⟨e, c⟩ := ec
    obtain ⟨_, T', hT', _, hcov, _⟩ := e2eCheck_sound h
    rw [hT] at hT'
    have : T = T' := Option.some.inj hT'
    subst this
    exact absurd hcov (hna e)

theorem e2eCheck_halt_none {tDigest tB pB iB : Bytes} {inst : InstanceCommitment}
    {T : Transcript fx.Item} (hT : decodeTranscript fxItemC tB = some T) {r : HaltReason}
    (h : coverageCheck fx inst pB T = .halt r) : e2eCheck tDigest tB pB iB inst = none :=
  e2eCheck_none_of_not_accept hT (by intro e he; rw [h] at he; cases he)

theorem e2eCheck_reject_none {tDigest tB pB iB : Bytes} {inst : InstanceCommitment}
    {T : Transcript fx.Item} (hT : decodeTranscript fxItemC tB = some T) {r : RejectReason}
    (h : coverageCheck fx inst pB T = .reject r) : e2eCheck tDigest tB pB iB inst = none :=
  e2eCheck_none_of_not_accept hT (by intro e he; rw [h] at he; cases he)

end P10S2
