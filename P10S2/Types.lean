import P10.Bound

/-!
# P10S2.Types — core data of the S2a coverage kernel

Everything in this file is plain data. No cryptographic fact is asserted here:
`SigObservation` is an uninterpreted observation supplied by S2b (prereg TB2);
Lean alone decides authorization, relevance and lifecycle validity.

Bytes are `List Nat` (as in frozen S1) so that the kernel can evaluate everything.
-/

namespace P10S2

abbrev Bytes := List Nat

structure Digest where
  bytes : Bytes
  deriving DecidableEq, Repr

structure Iss where
  bytes : Bytes
  deriving DecidableEq, Repr

structure Subject where
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Statement kinds (prereg §6). -/
inductive Kind
  | profileCommit
  | instanceCommit
  | admission
  | closure
  | adjudication
  deriving DecidableEq, Repr

/-- Pure cryptographic observation reported by S2b (prereg TB2). Never a verdict. -/
inductive SigObservation
  | verified
  | badSignature
  | keyUnavailable
  deriving DecidableEq, Repr

/-- `InstanceCommitment` with the normative fields of profile v0.1.1 §2.3. -/
structure InstanceCommitment where
  requestId                   : Bytes
  issuerId                    : Iss
  instanceSubject             : Subject
  instanceOwnerIss            : Iss
  logIdentityDigest           : Digest
  leafEncodingProfileDigest   : Digest
  claimDigest                 : Digest
  profileDigest               : Digest
  evidenceScopeDigest         : Digest
  admissionRuleDigest         : Digest
  coverageRuleDigest          : Digest
  authorizedAdmitterSetDigest : Digest
  subjectDerivationDigest     : Digest
  deriving DecidableEq, Repr

/-- `EvidenceClosure` payload (profile §2.6). -/
structure ClosurePayload where
  instanceSubject                      : Subject
  terminal                             : Bool
  orderedAdmissionRefs                 : List Nat
  closedEvidenceSetDigest              : Digest
  checkpointPreclosureTranscriptDigest : Digest
  deriving DecidableEq, Repr

/-- Decoded statement payloads (typed by S2b; Lean checks them against `Kind`). -/
inductive Payload (Item : Type)
  | profileCommit  (profileDigest : Digest)
  | instanceCommit (ic : InstanceCommitment)
  | admission      (item : Item)
  | closure        (cl : ClosurePayload)
  | adjudication   (profileRef commitRef closureRef : Nat)
  deriving DecidableEq, Repr

def Payload.kind {Item : Type} : Payload Item → Kind
  | .profileCommit _ => .profileCommit
  | .instanceCommit _ => .instanceCommit
  | .admission _ => .admission
  | .closure _ => .closure
  | .adjudication _ _ _ => .adjudication

/-- Everything the verifier can observe about one leaf of the log (prereg TB2). -/
structure LeafFacts (Item : Type) where
  sub     : Subject
  iss     : Iss
  kind    : Kind
  sig     : SigObservation
  payload : Option (Payload Item)
  deriving DecidableEq, Repr

/-- Abstract log view through `S_R`: `none` = not obtainable by the verifier. -/
structure LogView (Item : Type) where
  size : Nat
  leaf : Nat → Option (LeafFacts Item)

inductive RowStatus
  | available (sub : Subject)
  | unavailable
  deriving DecidableEq, Repr

structure Row where
  idx    : Nat
  status : RowStatus
  deriving DecidableEq, Repr

structure DetailedEntry (Item : Type) where
  idx     : Nat
  iss     : Iss
  kind    : Kind
  sig     : SigObservation
  payload : Option (Payload Item)
  deriving DecidableEq, Repr

structure Checkpoint where
  size       : Nat
  rootDigest : Digest
  deriving DecidableEq, Repr

structure Transcript (Item : Type) where
  logIdentityDigest   : Digest
  keyResolutionDigest : Digest
  checkpoint          : Checkpoint
  rows                : List Row
  detailed            : List (DetailedEntry Item)
  deriving DecidableEq, Repr

/-- REJECT reasons, named by the prereg condition that produces them. -/
inductive RejectReason
  | c1_rowsNotContiguous
  | c1_detailedMismatch
  | c1_logIdentity
  | c1_profileDigest
  | c1_profileDecode
  | c1_profileFields
  | c1_keyResolutionDigest
  | c1_admitterSetDigest
  | c3_profileAfterFirstAdmission
  | c4_multipleCommitments
  | c4_commitmentMismatch
  | c4_commitmentAfterFirstAdmission
  | c5_citesNonOwnerLifecycle
  | c6_multipleClosures
  | c7_refsNotStrictlyAscending
  | c8_refNotRelevantAdmission
  | c9_refsNotExactRelevantSet
  | c10_relevantAdmissionAfterClosure
  | c12_evidenceOutsideE
  deriving DecidableEq, Repr

/-- HALT reasons: unavailable verification input, never negative evidence. -/
inductive HaltReason
  | c2_rowUnavailable
  | c2_subjectPayloadUnavailable
  | c2_keyUnavailable
  | c3_noProfileCommitment
  | c4_noInstanceCommitment
  | c6_noValidClosure
  | c11_noAdjudicationAfterClosure
  | tb5_checkpointMaterialUnavailable
  deriving DecidableEq, Repr

/-- Coverage outcome. `halt` carries no evidence, by type (prereg §10). -/
inductive CoverageOutcome (Evidence : Type)
  | accept (e : Evidence)
  | reject (r : RejectReason)
  | halt   (r : HaltReason)
  deriving DecidableEq, Repr

end P10S2
