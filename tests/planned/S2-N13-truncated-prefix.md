# S2-N13 — Truncated prefix

**Status: PLANNED (specification only; no Lean test exists).**

## Scenario
Transcript ends at the closure although checkpoint S_R commits to a larger tree containing another relevant admission.

## Future expected result
REJECT/HALT according to the missing-material condition; never ACCEPT
