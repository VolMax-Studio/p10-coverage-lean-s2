# S1 dependency (single source of truth)

```
repo:   VolMax-Studio/p10-underdetermination-lean-s1
kind:   commit            # change to `tag` when the human S1 freeze tag exists
pin:    e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1
```

- S1 status at this pin: implementation closed; post-merge CI PASS;
  adversarial gate `SURVIVES-REVIEW`; **not human-ratified** in this record.
- No tag is invented here. Changing `kind`/`pin` above must not require any
  change to semantic Lean code.
- Toolchain mirrored from S1 at the pin: `leanprover/lean4:v4.33.0`;
  `autoImplicit = false`.
- **No Lake `require` is declared yet.** The S1 modules (`P10.Bound`,
  `P10.Certificate`, …) are not imported by any S2a file at scaffold stage.
  How the pin becomes a Lake-level dependency is an open decision for the
  Composition task; do not add it ad hoc.
