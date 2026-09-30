import P10S2Tests.Common

/-!
# P10S2Tests.Model — the concrete fixture scenarios (vector side)

Builds every vector's objects from a small scenario language. The generator (`Gen.lean`)
encodes them with the checker's own codecs. Nothing here is covered by the verifier manifest.
-/

namespace P10S2Tests
open P10S2 P10.Sha256

def mkTok (b : Bytes) (h : allTokB b = true := by decide) : Tok := ⟨b, h⟩

def ownerIss : Iss := ⟨bytes% "issuer-owner"⟩
def adm1 : Iss := ⟨bytes% "admitter-one"⟩
def adm2 : Iss := ⟨bytes% "admitter-two"⟩
def intruder : Iss := ⟨bytes% "intruder-x"⟩
def reqId : Bytes := bytes% "req-0001"
/-- The instance subject is derived (prereg v0.2.5 B2), never a free constant. -/
def subj : Subject := subjectDeriveV0 ownerIss reqId
def siblingSub : Subject := ⟨bytes% "p10s2sub:sibling-0002"⟩
def subjOffByOne : Subject := ⟨(subjectDeriveV0 ownerIss reqId).bytes.dropLast ++ [48]⟩

/-- `intruder-x` has a key (key availability) but is NOT an authorized admitter (G6-B2). -/
def keyRes : KeyResolution :=
  ⟨[(mkTok (bytes% "admitter-one"), mkTok (bytes% "fp-adm1-01")),
    (mkTok (bytes% "admitter-two"), mkTok (bytes% "fp-adm2-01")),
    (mkTok (bytes% "intruder-x"), mkTok (bytes% "fp-intr-01")),
    (mkTok (bytes% "issuer-owner"), mkTok (bytes% "fp-own-01"))], by decide⟩

/-- Same identities, different key material (S2-N9). -/
def keyResAlt : KeyResolution :=
  ⟨[(mkTok (bytes% "admitter-one"), mkTok (bytes% "fp-adm1-XX")),
    (mkTok (bytes% "admitter-two"), mkTok (bytes% "fp-adm2-01")),
    (mkTok (bytes% "intruder-x"), mkTok (bytes% "fp-intr-01")),
    (mkTok (bytes% "issuer-owner"), mkTok (bytes% "fp-own-01"))], by decide⟩

/-- `admitter-two` has no key (S2-N31). -/
def keyResNo2 : KeyResolution :=
  ⟨[(mkTok (bytes% "admitter-one"), mkTok (bytes% "fp-adm1-01")),
    (mkTok (bytes% "issuer-owner"), mkTok (bytes% "fp-own-01"))], by decide⟩

def admittersStd : AuthorizedAdmitters :=
  ⟨[mkTok (bytes% "admitter-one"), mkTok (bytes% "admitter-two")], by decide⟩

/-- Invalid by schema: the owner is listed as an admitter. -/
def admittersWithOwner : AuthorizedAdmitters :=
  ⟨[mkTok (bytes% "admitter-one"), mkTok (bytes% "admitter-two"), mkTok (bytes% "issuer-owner")],
    by decide⟩

def admSet : List Iss := [adm1, adm2]

/-- The concrete profile artifact; `md` is the `VerifierManifestS2aV0` digest (hex token), `ls`
the `LeafEncodeSpecArtifactDigestV0` of the frozen spec file (hex token). -/
def profileOf (md ls : Tok) (kr : KeyResolution := keyRes)
    (admitters : AuthorizedAdmitters := admittersStd)
    (fixtureId : Tok := mkTok fx.fixtureId) (spec : Tok := mkTok P10.Wire.specTok)
    (s1tok : Tok := mkTok P10.Wire.profileTok)
    (mref : Tok := mkTok (bytes% "VerifierManifestS2aV0.json")) : ProfileArtifact :=
  { admissionRuleId := mkTok (bytes% "admission-rules-v0")
    authorizedAdmitters := admitters
    checkpointVds := mkTok (bytes% "rfc9162-sha256-vds1")
    coverageRuleId := mkTok (bytes% "coverage-rules-v0")
    evidenceScopeRuleId := mkTok (bytes% "evidence-scope-v0")
    fixtureId := fixtureId, keyResolution := kr
    leafEncodingSpecDigest := ls
    normativeProfileDigest := spec, s1ProfileToken := s1tok
    verifierManifestDigest := md, verifierManifestRef := mref }

/-- The frozen commitment consistent with a profile artifact (all §6b descriptors derived). -/
def instOfProf (prof : ProfileArtifact) : InstanceCommitment :=
  { requestId := reqId, issuerId := ownerIss, instanceSubject := subj
    instanceOwnerIss := ownerIss
    logIdentityDigest := ⟨bytes% "log-identity-v0"⟩
    leafEncodingProfileDigest := leafEncodingProfileDigestV0 prof
    claimDigest := claimDigestV0 .secondBit
    profileDigest := ⟨sha256 (encodeProfileArtifact prof)⟩
    evidenceScopeDigest := evidenceScopeDigestV0 prof
    admissionRuleDigest := admissionRuleDigestV0 prof
    coverageRuleDigest := coverageRuleDigestV0 prof
    authorizedAdmitterSetDigest := authorizedAdmittersDigestOf prof
    subjectDerivationDigest := subjectDerivationDigestV0 prof }

/-- Legacy (v0.2.4) binary digest forms, used only by the negative vectors N34 and N35. -/
def legacyPreclosure (v : List (Nat × Kind × Iss)) : Digest :=
  ⟨sha256 (bytes% "P10S2-PreclosureView-v0:" ++
    (Codec.list (Codec.prod Codec.nat (Codec.prod cKind cIss))).enc v)⟩
def legacyKeyRes (kr : KeyResolution) : Digest := ⟨sha256 (keyResolutionC.enc kr)⟩

/-- One leaf of the scenario log. -/
inductive Leaf
  | e (iss : Iss) (kind : Kind) (sig : SigObservation) (payload : Option (Payload FxItem))
  | other (sub : Subject)
  | unavail

def buildT (inst : InstanceCommitment) (krDigest : Digest) (leaves : List Leaf) (size : Nat) :
    Transcript FxItem :=
  let idxd := (List.range leaves.length).zip leaves
  { logIdentityDigest := inst.logIdentityDigest
    keyResolutionDigest := krDigest
    checkpoint := ⟨size, ⟨bytes% "root-digest-placeholder"⟩⟩
    rows := idxd.map fun p =>
      ⟨p.1, match p.2 with
        | .e _ _ _ _ => .available inst.instanceSubject
        | .other s => .available s
        | .unavail => .unavailable⟩
    detailed := idxd.filterMap fun p =>
      match p.2 with
      | .e iss k s pl => some ⟨p.1, iss, k, s, pl⟩
      | _ => none }

def krDigestOf : Digest := keyResolutionDigestV0 keyRes

def tOf' (inst : InstanceCommitment) (krd : Digest) (leaves : List Leaf) : Transcript FxItem :=
  buildT inst krd leaves leaves.length

def tOf (inst : InstanceCommitment) (leaves : List Leaf) : Transcript FxItem :=
  tOf' inst krDigestOf leaves

/-- The closure-transcript view right before a closure placed after `before`. -/
def viewBefore (inst : InstanceCommitment) (before : List Leaf) : List (Nat × Kind × Iss) :=
  let W := viewT inst.instanceSubject (tOf inst before)
  closureView ⟨fx.admissible, inst, admSet⟩ W W.size

/-- Pre-closure digest for a closure placed right after `before` (profile M29). -/
def digestBefore (inst : InstanceCommitment) (before : List Leaf) : Digest :=
  preclosureDigestV0 (viewBefore inst before)

def lf_pc (inst : InstanceCommitment) : Leaf :=
  .e ownerIss .profileCommit .verified (some (.profileCommit inst.profileDigest))
def lf_pc_other : Leaf :=
  .e ownerIss .profileCommit .verified (some (.profileCommit ⟨bytes% "other-profile-digest"⟩))
def lf_ic (inst : InstanceCommitment) : Leaf :=
  .e ownerIss .instanceCommit .verified (some (.instanceCommit inst))
def adm (iss : Iss) (it : FxItem) : Leaf :=
  .e iss .admission .verified (some (.admission it))
def a1 : Leaf := adm adm1 (.first false)
def a2 : Leaf := adm adm1 (.second false)
def a2' : Leaf := adm adm2 (.second false)
def a3 : Leaf := adm adm2 (.first true)
/-- `EvidenceDigestV0` of an S1 evidence value. -/
def evD (e : P10.S1.Evidence) : Digest := evidenceDigestV0 (P10.Wire.evidenceTok e)
def dU : Digest := evD (.obs false none)
def dD : Digest := evD (.obs false (some false))
def dI : Digest := evD .inconsistent
def lf_closure (inst : InstanceCommitment) (before : List Leaf) (refs : List Nat)
    (cd : Digest := dU) : Leaf :=
  .e ownerIss .closure .verified
    (some (.closure ⟨inst.instanceSubject, true, refs, cd, digestBefore inst before⟩))
def lf_adj (a b c : Nat) : Leaf := .e ownerIss .adjudication .verified (some (.adjudication a b c))

/-- `pre` = leaves before the closure (profile and commitment already included). -/
def withClosure (inst : InstanceCommitment) (pre : List Leaf) (refs : List Nat)
    (cd : Digest := dU) : List Leaf :=
  pre ++ [lf_closure inst pre refs cd, lf_adj 0 1 pre.length]

/-- Standard skeleton: profile, commitment, `mid`, closure over `refs`, adjudication. -/
def standard (inst : InstanceCommitment) (mid : List Leaf) (refs : List Nat)
    (cd : Digest := dU) : List Leaf :=
  withClosure inst ([lf_pc inst, lf_ic inst] ++ mid) refs cd

end P10S2Tests
