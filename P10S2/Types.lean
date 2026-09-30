/-!
# P10S2.Types

Identifiers and the outcome type for S2a. SCAFFOLD ONLY: no coverage logic.

Nothing here implies cryptographic validity; all such facts are produced by
S2b (`p10-replay-verifier`) and arrive as explicit typed inputs.
-/

namespace P10S2

/-- Raw bytes. -/
abbrev Bytes := List UInt8

/-- Identity of a transparency log (committed in the instance commitment). -/
structure LogId where
  bytes : Bytes
  deriving DecidableEq, Repr

/-- A digest (e.g. tree root, policy digest). Length/algorithm not fixed here. -/
structure Digest where
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Authenticated issuer identifier (`iss`). -/
structure Iss where
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Authenticated subject identifier (`sub`). -/
structure Subject where
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Leaf / registration index in the log. -/
abbrev Idx := Nat

/-- Statement kinds (prereg v0.1 §6). -/
inductive Kind
  | profileCommit
  | instanceCommit
  | admission
  | closure
  | adjudication
  deriving DecidableEq, Repr

/-- The frozen instance commitment: identities Lean must match against.
Field semantics are NOT yet specified (prereg v0.2 is a draft). -/
structure InstanceCommitment where
  logId              : LogId
  subject            : Subject
  profileDigest      : Digest
  admissionRulesDigest : Digest
  scopeDigest        : Digest
  authPolicyDigest   : Digest
  keyResolutionDigest : Digest
  deriving DecidableEq, Repr

/-- Reasons for REJECT. Names reserve the vocabulary only; no semantics yet. -/
inductive RejectReason
  | commitmentConflict
  | profileMismatch
  | checkpointLogMismatch
  | keyMapMismatch
  | closureConflict
  | closureRefsInvalid
  | omittedRelevantAdmission
  | relevantAdmissionAfterClosure
  | citedEntryNotRelevant
  | bundleObligationFailed
  | s1EvidenceBindingMismatch
  deriving DecidableEq, Repr

/-- Reasons for HALT (unavailable verification input; never negative evidence). -/
inductive HaltReason
  | noCommitment
  | noClosure
  | payloadUnavailable
  | prefixIncomplete
  | checkpointMaterialUnavailable
  deriving DecidableEq, Repr

/-- Coverage outcome. `halt` carries no evidence and no verdict, by type. -/
inductive CoverageOutcome (Evidence : Type)
  | accept (e : Evidence)
  | reject (reason : RejectReason)
  | halt   (reason : HaltReason)

end P10S2
