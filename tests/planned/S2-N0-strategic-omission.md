# S2-N0 — Strategic omission

**Status: PLANNED (specification only; no Lean test exists).**

## Scenario
Registered, in-policy complete evidence contains both the weaker and the determining information (e.g. A1=first:false, A2=second:false; Bundle([A1])=eU, Bundle([A1,A2])=eD). The closure references only the admission(s) yielding eU.

## Future expected result
REJECT

## Notes
Must fail against the S2∘S1 composition theorem, not only a checker unit test. Scope: registered, in-policy omission only.
