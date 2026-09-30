import P10S2.Fixture
import P10S2.TranscriptCodec
import P10S2.ProfileArtifact
import P10.Sha256

/-!
# P10S2.Coverage — Lean-side classification and `coverageCheck` (prereg §6, §7)

S2b supplies observations only (`SigObservation`, availability). Lean decides authorization,
relevance, lifecycle validity, closure validity and REJECT vs HALT.

Evaluation order is the order of the table in prereg §7: C1 (malformed / foreign transcript)
precedes C2 (availability), and C3–C12 follow in table order.

Everything here is structurally recursive and kernel-evaluable.
-/

namespace P10S2
open P10.Sha256 (sha256)

variable {Item : Type}

/-! ### Classification of one leaf's facts -/

def lifecycleKind : Kind → Bool
  | .profileCommit => true
  | .instanceCommit => true
  | .admission => false
  | .closure => true
  | .adjudication => true

/-- The typed payload is of the claimed kind. -/
def kindMatches (lf : LeafFacts Item) : Bool :=
  match lf.payload with
  | some p => decide (p.kind = lf.kind)
  | none => false

/-- Valid owner-signed lifecycle entry: owner `iss`, signature observed valid, lifecycle kind,
payload of that kind. -/
def validOwnerLifecycleF (owner : Iss) (lf : LeafFacts Item) : Bool :=
  decide (lf.iss = owner) && decide (lf.sig = .verified) && lifecycleKind lf.kind &&
    kindMatches lf

/-- `RelevantAdmissionπ` (profile §2.6) for a subject leaf: kind `admission`, `iss` in the
committed admitter set, signature valid, payload accessible and admissible. -/
def relevantF (admissible : Item → Bool) (adm : List Iss) (lf : LeafFacts Item) : Bool :=
  decide (lf.kind = .admission) && adm.contains lf.iss && decide (lf.sig = .verified) &&
    (match lf.payload with
     | some (.admission it) => admissible it
     | _ => false)

/-- Everything Lean needs besides the log: admissibility, the frozen commitment, the admitter set. -/
structure Ctx (Item : Type) where
  admissible : Item → Bool
  inst       : InstanceCommitment
  adm        : List Iss

def Ctx.owner (c : Ctx Item) : Iss := c.inst.instanceOwnerIss

/-! ### Per-index classification over a (subject) log view -/

def relevantAt (c : Ctx Item) (W : LogView Item) (i : Nat) : Bool :=
  match W.leaf i with
  | some lf => relevantF c.admissible c.adm lf
  | none => false

/-- Valid owner profile commitment for this instance's profile digest. -/
def profileAt (c : Ctx Item) (W : LogView Item) (i : Nat) : Bool :=
  match W.leaf i with
  | some lf =>
    validOwnerLifecycleF c.owner lf && decide (lf.kind = .profileCommit) &&
      (match lf.payload with
       | some (.profileCommit d) => decide (d = c.inst.profileDigest)
       | _ => false)
  | none => false

/-- Valid owner `InstanceCommitment` for the instance tuple `(owner, request_id, subject)`. -/
def commitAt (c : Ctx Item) (W : LogView Item) (i : Nat) : Option InstanceCommitment :=
  match W.leaf i with
  | some lf =>
    if validOwnerLifecycleF c.owner lf && decide (lf.kind = .instanceCommit) then
      match lf.payload with
      | some (.instanceCommit ic) =>
        if ic.instanceOwnerIss = c.inst.instanceOwnerIss ∧ ic.requestId = c.inst.requestId ∧
            ic.instanceSubject = c.inst.instanceSubject then some ic else none
      | _ => none
    else none
  | none => none

/-- Non-owner lifecycle entry (excluded from all counts; citing it REJECTs). -/
def nonOwnerLifecycleAt (c : Ctx Item) (W : LogView Item) (i : Nat) : Bool :=
  match W.leaf i with
  | some lf => lifecycleKind lf.kind && decide (lf.iss ≠ c.owner)
  | none => false

/-- Valid owner adjudication with the three references it cites. -/
def adjAt (c : Ctx Item) (W : LogView Item) (i : Nat) : Option (Nat × Nat × Nat) :=
  match W.leaf i with
  | some lf =>
    if validOwnerLifecycleF c.owner lf && decide (lf.kind = .adjudication) then
      match lf.payload with
      | some (.adjudication a b d) => some (a, b, d)
      | _ => none
    else none
  | none => none

/-! ### The pre-closure transcript digest (profile M29) -/

/-- Entries of `ClosureTranscriptViewπ` strictly before `k`: valid owner lifecycle entries or
relevant admissions, as `(index, kind, iss)`. -/
def closureView (c : Ctx Item) (W : LogView Item) (k : Nat) : List (Nat × Kind × Iss) :=
  (List.range k).filterMap fun i =>
    match W.leaf i with
    | some lf =>
      if relevantF c.admissible c.adm lf || validOwnerLifecycleF c.owner lf
      then some (i, lf.kind, lf.iss) else none
    | none => none

def preclosureMagic : Bytes := bytes% "P10S2-PreclosureView-v0:"

def viewC : Codec (List (Nat × Kind × Iss)) :=
  Codec.list (Codec.prod Codec.nat (Codec.prod cKind cIss))

def preclosureDigestOf (v : List (Nat × Kind × Iss)) : Digest :=
  ⟨sha256 (preclosureMagic ++ viewC.enc v)⟩

/-- Valid owner closure at `k` (M29: its pre-closure digest describes the view right before `k`). -/
def closureAt (c : Ctx Item) (W : LogView Item) (k : Nat) : Option ClosurePayload :=
  match W.leaf k with
  | some lf =>
    if validOwnerLifecycleF c.owner lf && decide (lf.kind = .closure) then
      match lf.payload with
      | some (.closure cl) =>
        if cl.instanceSubject = c.inst.instanceSubject ∧ cl.terminal = true ∧
            cl.checkpointPreclosureTranscriptDigest = preclosureDigestOf (closureView c W k)
        then some cl else none
      | _ => none
    else none
  | none => none

def itemAt (W : LogView Item) (i : Nat) : Option Item :=
  match W.leaf i with
  | some lf => (match lf.payload with | some (.admission it) => some it | _ => none)
  | none => none

def strictAscNat : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && strictAscNat (y :: rest)

/-! ### Stage results -/

abbrev Stop (E : Type) := Option (CoverageOutcome E)

def stage {E : Type} (ok : Bool) (o : CoverageOutcome E) : Stop E := if ok then none else some o

def finish {E : Type} : Stop E → CoverageOutcome E → CoverageOutcome E
  | some o, _ => o
  | none, k => k

/-! ### C3 – C12 over the subject view -/

/-- `i` precedes every RelevantAdmission of the view. -/
def beforeAll (c : Ctx Item) (W : LogView Item) (i : Nat) : Bool :=
  ((List.range W.size).filter (relevantAt c W)).all fun f => decide (i < f)

def coreCheck (π : AdmissionProfile) (c : Ctx π.Item) (W : LogView π.Item) :
    CoverageOutcome π.Evidence :=
  let idxs := List.range W.size
  let profs := idxs.filter (profileAt c W)
  let commits := idxs.filterMap fun i => (commitAt c W i).map fun ic => (i, ic)
  let adjs := idxs.filterMap fun i => (adjAt c W i).map fun r => (i, r)
  let closures := idxs.filterMap fun i => (closureAt c W i).map fun cl => (i, cl)
  -- C3: profile commitment registered before the first RelevantAdmission (M5)
  match profs with
  | [] => .halt .c3_noProfileCommitment
  | p :: _ =>
  finish (stage (beforeAll c W p) (.reject .c3_profileAfterFirstAdmission)) <|
  -- C4: exactly one valid owner InstanceCommitment, before the first admission
  match commits with
  | [] => .halt .c4_noInstanceCommitment
  | _ :: _ :: _ => .reject .c4_multipleCommitments
  | [(ci, ic)] =>
  finish (stage (decide (ic = c.inst)) (.reject .c4_commitmentMismatch)) <|
  finish (stage (beforeAll c W ci) (.reject .c4_commitmentAfterFirstAdmission)) <|
  -- C5: a valid owner object citing a non-owner lifecycle entry REJECTs (M28)
  finish (stage (adjs.all fun ar =>
      !nonOwnerLifecycleAt c W ar.2.1 && !nonOwnerLifecycleAt c W ar.2.2.1 &&
      !nonOwnerLifecycleAt c W ar.2.2.2) (.reject .c5_citesNonOwnerLifecycle)) <|
  -- C6: exactly one valid owner closure
  match closures with
  | [] => .halt .c6_noValidClosure
  | _ :: _ :: _ => .reject .c6_multipleClosures
  | [(k, cl)] =>
  let R := cl.orderedAdmissionRefs
  -- C7: strictly ascending (hence duplicate-free)
  finish (stage (strictAscNat R) (.reject .c7_refsNotStrictlyAscending)) <|
  -- C8: every ref is a RelevantAdmission
  finish (stage (R.all (relevantAt c W)) (.reject .c8_refNotRelevantAdmission)) <|
  -- C9: refs are exactly the RelevantAdmissions before the closure
  finish (stage (decide (R = (List.range k).filter (relevantAt c W)))
    (.reject .c9_refsNotExactRelevantSet)) <|
  -- C10: no RelevantAdmission after the closure and before size(S_R)
  finish (stage (!(idxs.any fun i => decide (k < i) && relevantAt c W i))
    (.reject .c10_relevantAdmissionAfterClosure)) <|
  -- C11: a valid owner adjudication after the closure (else HALT)
  finish (stage (adjs.any fun ar => decide (k < ar.1))
    (.halt .c11_noAdjudicationAfterClosure)) <|
  -- C12: e = Bundle(refs) ∈ Eπ
  let e := π.bundle (R.filterMap (itemAt W))
  if π.inEb e = true then .accept e else .reject .c12_evidenceOutsideE

/-! ### The subject view of a transcript, and C1 / C2 -/

def toFacts (sub : Subject) (d : DetailedEntry Item) : LeafFacts Item :=
  ⟨sub, d.iss, d.kind, d.sig, d.payload⟩

/-- The subject view the transcript itself presents (rows of other subjects are invisible). -/
def viewT (sub : Subject) (T : Transcript Item) : LogView Item where
  size := T.checkpoint.size
  leaf i :=
    if i < T.checkpoint.size then
      ((T.detailed.find? fun d => decide (d.idx = i)).map (toFacts sub))
    else none

/-- Indices of the available rows whose `sub` equals the instance subject. -/
def matchIdxs (sub : Subject) (rows : List Row) : List Nat :=
  rows.filterMap fun r =>
    match r.status with
    | .available s => if s = sub then some r.idx else none
    | .unavailable => none

def rowUnavailable (r : Row) : Bool :=
  match r.status with
  | .unavailable => true
  | .available _ => false

def authorizedIss (c : Ctx Item) (i : Iss) : Bool := decide (i = c.owner) || c.adm.contains i

/-- Admitter set: every `iss` of `KeyResolutionV0` other than the owner. -/
def admittersOf (owner : Iss) (kr : KeyResolution) : List Iss :=
  kr.1.filterMap fun e => if Iss.mk e.1.1 = owner then none else some ⟨e.1.1⟩

def admitterSetMagic : Bytes := bytes% "P10S2-AdmitterSet-v0:"

def admitterSetDigestOf (adm : List Iss) : Digest :=
  ⟨sha256 (admitterSetMagic ++ (Codec.list cIss).enc adm)⟩

def keyResolutionDigestOf (kr : KeyResolution) : Digest := ⟨sha256 (keyResolutionC.enc kr)⟩

/-- S1 constants a profile artifact must carry. -/
def s1Spec : Bytes := P10.Wire.specTok
def s1ProfileTok : Bytes := P10.Wire.profileTok

/-- The transcript-level checks C1 and C2 and then the core. `pB` and `T` are inputs. -/
def coverageCheck (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Transcript π.Item) : CoverageOutcome π.Evidence :=
  let sub := inst.instanceSubject
  -- C1 (structural): contiguity, row/detail correspondence, log identity
  finish (stage (decide (T.rows.map Row.idx = List.range T.checkpoint.size))
    (.reject .c1_rowsNotContiguous)) <|
  finish (stage (decide (T.detailed.map DetailedEntry.idx = matchIdxs sub T.rows))
    (.reject .c1_detailedMismatch)) <|
  finish (stage (decide (T.logIdentityDigest = inst.logIdentityDigest))
    (.reject .c1_logIdentity)) <|
  -- C1 (profile artifact): digest, strict decode, fields, key resolution, admitter set
  finish (stage (decide (sha256 pB = inst.profileDigest.bytes)) (.reject .c1_profileDigest)) <|
  match decodeProfileArtifact pB with
  | none => .reject .c1_profileDecode
  | some prof =>
  finish (stage (decide (prof.fixtureId.1 = π.fixtureId) &&
      decide (prof.normativeProfileDigest.1 = s1Spec) &&
      decide (prof.s1ProfileToken.1 = s1ProfileTok)) (.reject .c1_profileFields)) <|
  finish (stage (decide (T.keyResolutionDigest = keyResolutionDigestOf prof.keyResolution))
    (.reject .c1_keyResolutionDigest)) <|
  let adm := admittersOf inst.instanceOwnerIss prof.keyResolution
  finish (stage (decide (inst.authorizedAdmitterSetDigest = admitterSetDigestOf adm))
    (.reject .c1_admitterSetDigest)) <|
  let c : Ctx π.Item := ⟨π.admissible, inst, adm⟩
  -- C2: availability (HALT)
  finish (stage (!(T.rows.any rowUnavailable)) (.halt .c2_rowUnavailable)) <|
  finish (stage (T.detailed.all fun d => d.payload.isSome)
    (.halt .c2_subjectPayloadUnavailable)) <|
  finish (stage (T.detailed.all fun d =>
      !(authorizedIss c d.iss && decide (d.sig = .keyUnavailable))) (.halt .c2_keyUnavailable)) <|
  coreCheck π c (viewT sub T)

/-- When S2b cannot produce a transcript at all (checkpoint material missing): HALT (TB5). -/
def coverageCheckM (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Option (Transcript π.Item)) : CoverageOutcome π.Evidence :=
  match T with
  | none => .halt .tb5_checkpointMaterialUnavailable
  | some T => coverageCheck π inst pB T

end P10S2
