# S2-N14 — Classification misbinding

**Status: PLANNED (specification only; no Lean test exists).**

## Scenario
S2b-supplied classification is wrong: a relevant admission's Kind is tagged differently (e.g. adjudication), or its subject is spoofed to a sibling so exclusion drops it. Kind/sub must be checked against authenticated payload.

## Future expected result
REJECT/HALT; never ACCEPT with the entry silently dropped
