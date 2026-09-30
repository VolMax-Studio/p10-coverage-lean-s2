import P10S2.Types
import P10S2.Checkpoint

/-!
# P10S2.Transcript

A transcript is NOT a bare `List Entry`. It carries the checkpoint `S_R`, a
summary row for every leaf in `[0, size(S_R))`, and raw entry facts for
matching-subject leaves. Status is typed so that Lean, not S2b, decides
authorization, relevance, REJECT vs HALT. S2b must not pre-filter.

STRUCTURES ONLY. Contiguity / completeness predicates are future work
(see profile/TRUST_BOUNDARIES.md).
-/

namespace P10S2

/-- Signature status under the frozen key map, attested by S2b. -/
inductive SigStatus
  | valid
  | badSignature
  | payloadUnavailable
  deriving DecidableEq, Repr

/-- One summary row per leaf: (index, protected `sub`). -/
structure LeafSummary where
  idx : Idx
  sub : Subject
  deriving DecidableEq, Repr

/-- Raw facts about a matching-subject leaf. `claimedKind` is a claim only;
Lean must eventually cross-check it against the payload bytes. -/
structure RawEntry where
  idx         : Idx
  iss         : Iss
  sub         : Subject
  claimedKind : Kind
  payload     : Bytes
  sigStatus   : SigStatus
  deriving DecidableEq, Repr

/-- Checkpoint-bound transcript. -/
structure Transcript where
  checkpoint : Checkpoint
  summaries  : List LeafSummary
  entries    : List RawEntry
  deriving DecidableEq, Repr

end P10S2
