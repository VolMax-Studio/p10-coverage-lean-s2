# P10 S2a axiom and source policy

Covered by `axiom_policy_digest` of `VerifierManifestS2aV0`.

**Permitted axioms** for every exported theorem (`#print axioms`): `propext`,
`Classical.choice`, `Quot.sound`. (Frozen S1 is axiom-free by its own stricter policy; S2a's
proofs use `simp`/`omega` and structural lemmas and therefore the three standard axioms.)

**Forbidden** anywhere in S2a sources: `sorry`, `admit`, `sorryAx`, `native_decide`,
`Lean.ofReduceBool`, `axiom` declarations, `unsafe`, `implemented_by`, `extern`, `opaque`,
`partial`, `macro`, `elab`, `syntax`, `notation`, `unif_hint`, `run_cmd`, `initialize`,
`import Lean`, `open Lean`, `addDecl`, any `set_option` other than `maxRecDepth`.
`scripts/check_no_forbidden_scope.py` enforces this (defence in depth; the boundary is the
kernel).

**`decide +kernel`** is permitted in the vector/test library only. It is kernel evaluation of a
`Decidable` instance (no `Lean.ofReduceBool`, no compiler, no extra axiom); the axiom audit and
`leanchecker` replay verify this. `native_decide` is never used.

**Elaboration-time metaprograms** are not written in S2a. The only ones used are frozen S1's
`bytes%`, `hex%`, `filebytes%` (S1 `P10/Bytes.lean`, part of the S1 TCB declared there).

**Kernel replay:** `leanchecker` over every module of the checker library `P10S2`.

**Audit completeness:** `P10S2/AxiomAudit.lean` is generated (`scripts/s2a.py gen-audit`) and the
acceptance command requires it to list exactly the non-private theorems of the checker library.
