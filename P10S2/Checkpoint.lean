import P10S2.Types

/-!
# P10S2.Checkpoint

The checkpoint `S_R` a transcript is bound to. Verification of the checkpoint
signature and root reconstruction is S2b's job (TB2/TB3); this module only
names the data Lean reasons about.
-/

namespace P10S2

/-- Checkpoint `S_R`: committed log identity, tree size and root digest. -/
structure Checkpoint where
  logId : LogId
  size  : Nat
  root  : Digest
  deriving DecidableEq, Repr

end P10S2
