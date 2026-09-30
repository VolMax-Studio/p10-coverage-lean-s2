import P10S2.Types

/-!
# P10S2.Fixtures

Toy fixture DATA TYPES only (no positive/negative results are claimed).
`first=false` / `second=false` mirror the S2-N0 / S2-N11 scenarios.
-/

namespace P10S2

/-- Toy admission items for the two-bit fixture. -/
inductive ToyItem
  | first  (b : Bool)
  | second (b : Bool)
  deriving DecidableEq, Repr

end P10S2
