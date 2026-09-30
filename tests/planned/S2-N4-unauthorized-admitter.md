# S2-N4 — Unauthorized admitter

**Status: PLANNED (specification only; no Lean test exists).**

## Scenario
Matching subject, but issuer/key not authorized by the frozen policy. Lean (not S2b) must see the entry with its typed status and decide.

## Future expected result
Entry is not a RelevantAdmission; a closure citing it REJECTs (not HALT)
