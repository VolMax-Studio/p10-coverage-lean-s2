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
def subj : Subject := ⟨bytes% "p10-sub:req-0001"⟩
def siblingSub : Subject := ⟨bytes% "p10-sub:req-0002"⟩
def subjOffByOne : Subject := ⟨bytes% "p10-sub:req-0000"⟩

def keyRes : KeyResolution :=
  ⟨[(mkTok (bytes% "admitter-one"), mkTok (bytes% "fp-adm1-01")),
    (mkTok (bytes% "admitter-two"), mkTok (bytes% "fp-adm2-01")),
    (mkTok (bytes% "issuer-owner"), mkTok (bytes% "fp-own-01"))], by decide⟩

/-- Same identities, different key material (S2-N9). -/
def keyResAlt : KeyResolution :=
  ⟨[(mkTok (bytes% "admitter-one"), mkTok (bytes% "fp-adm1-XX")),
    (mkTok (bytes% "admitter-two"), mkTok (bytes% "fp-adm2-01")),
    (mkTok (bytes% "issuer-owner"), mkTok (bytes% "fp-own-01"))], by decide⟩

def admSet : List Iss := admittersOf ownerIss keyRes

/-- The concrete profile artifact; `md` is the `VerifierManifestS2aV0` digest (hex token). -/
def profileOf (md : Tok) (kr : KeyResolution := keyRes)
    (fixtureId : Tok := mkTok fx.fixtureId) (spec : Tok := mkTok P10.Wire.specTok)
    (s1tok : Tok := mkTok P10.Wire.profileTok)
    (mref : Tok := mkTok (bytes% "VerifierManifestS2aV0.json")) : ProfileArtifact :=
  { admissionRuleId := mkTok (bytes% "admission-rules-v0")
    checkpointVds := mkTok (bytes% "rfc9162-sha256-vds1")
    coverageRuleId := mkTok (bytes% "coverage-rules-v0")
    evidenceScopeRuleId := mkTok (bytes% "evidence-scope-v0")
    fixtureId := fixtureId, keyResolution := kr
    normativeProfileDigest := spec, s1ProfileToken := s1tok
    verifierManifestDigest := md, verifierManifestRef := mref }

def instOf (pB : Bytes) (adm : List Iss := admSet) : InstanceCommitment :=
  { requestId := bytes% "req-0001", issuerId := ownerIss, instanceSubject := subj
    instanceOwnerIss := ownerIss
    logIdentityDigest := ⟨bytes% "log-identity-v0"⟩
    leafEncodingProfileDigest := ⟨bytes% "leaf-encode-v0"⟩
    claimDigest := claimDigest .secondBit
    profileDigest := ⟨sha256 pB⟩
    evidenceScopeDigest := ⟨bytes% "evidence-scope-v0"⟩
    admissionRuleDigest := ⟨bytes% "admission-rules-v0"⟩
    coverageRuleDigest := ⟨bytes% "coverage-rules-v0"⟩
    authorizedAdmitterSetDigest := admitterSetDigestOf adm
    subjectDerivationDigest := ⟨bytes% "subject-derive-v0"⟩ }

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

def krDigestOf : Digest := keyResolutionDigestOf keyRes

def tOf (inst : InstanceCommitment) (leaves : List Leaf) : Transcript FxItem :=
  buildT inst krDigestOf leaves leaves.length

/-- Pre-closure digest for a closure placed right after `before` (profile M29). -/
def digestBefore (inst : InstanceCommitment) (before : List Leaf) : Digest :=
  let W := viewT inst.instanceSubject (tOf inst before)
  preclosureDigestOf (closureView ⟨fx.admissible, inst, admSet⟩ W W.size)

def lf_pc (inst : InstanceCommitment) : Leaf :=
  .e ownerIss .profileCommit .verified (some (.profileCommit inst.profileDigest))
def lf_ic (inst : InstanceCommitment) : Leaf :=
  .e ownerIss .instanceCommit .verified (some (.instanceCommit inst))
def adm (iss : Iss) (it : FxItem) : Leaf :=
  .e iss .admission .verified (some (.admission it))
def a1 : Leaf := adm adm1 (.first false)
def a2 : Leaf := adm adm1 (.second false)
def a2' : Leaf := adm adm2 (.second false)
def a3 : Leaf := adm adm2 (.first true)
def closedDigest : Digest := ⟨bytes% "closed-evidence-digest-carried"⟩
def lf_closure (inst : InstanceCommitment) (before : List Leaf) (refs : List Nat) : Leaf :=
  .e ownerIss .closure .verified
    (some (.closure ⟨inst.instanceSubject, true, refs, closedDigest, digestBefore inst before⟩))
def lf_adj (a b c : Nat) : Leaf := .e ownerIss .adjudication .verified (some (.adjudication a b c))

/-- `pre` = leaves before the closure (profile and commitment already included). -/
def withClosure (inst : InstanceCommitment) (pre : List Leaf) (refs : List Nat) : List Leaf :=
  pre ++ [lf_closure inst pre refs, lf_adj 0 1 pre.length]

/-- Standard skeleton: profile, commitment, `mid`, closure over `refs`, adjudication. -/
def standard (inst : InstanceCommitment) (mid : List Leaf) (refs : List Nat) : List Leaf :=
  withClosure inst ([lf_pc inst, lf_ic inst] ++ mid) refs

end P10S2Tests
