# S1 dependency (single source of truth)

S2 depends on the **frozen, human-ratified S1 release tag**. The peeled commit
is recorded for reproducibility only.

```
repo:                   VolMax-Studio/p10-underdetermination-lean-s1
kind:                   tag
tag:                    v0.1.0-s1-ratified
tag object:             7c3df437de454466b932a5d0dc889b3287c64e05
peeled commit:          e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1
verifier manifest SHA-256: 06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907
status:                 RATIFIED / FROZEN S1
```

- **The tag is immutable.** S2 depends on the tag
  `v0.1.0-s1-ratified`; the tag object and the peeled commit above are
  recorded so the dependency can be reproduced and checked. If the tag ever
  resolved to a different object or commit, the dependency is broken and must
  not be silently re-pinned.
- S1 is ratified by a human act. **S2 is not ratified**: nothing in this
  repository is ratified, and no S2 coverage theorem exists.
- The previous temporary raw-commit pin is the same commit as the peeled
  commit above, so no semantic code changed with this update.
- Toolchain mirrored from S1: `leanprover/lean4:v4.33.0`
  (conda-forge `lean4 4.33.0 build h6c1889d_0`); `autoImplicit = false`.
- **No Lake `require` is declared yet.** The S1 modules (`P10.Bound`,
  `P10.Certificate`, …) are not imported by any S2a file at scaffold stage.
  How the tag becomes a Lake-level dependency is an open decision for the
  Composition task; do not add it ad hoc.
