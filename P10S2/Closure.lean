import P10S2.Types

/-!
# P10S2.Closure

Shape of an owner closure payload. Validity (ordering, duplicates, lifecycle,
zero-vs-many closures, preclosure transcript digest) is decided by Lean in a
later task; nothing is checked here.
-/

namespace P10S2

/-- Decoded closure payload (fields only). -/
structure ClosurePayload where
  orderedAdmissionRefs : List Idx
  preclosureTranscriptDigest : Digest
  deriving DecidableEq, Repr

end P10S2
