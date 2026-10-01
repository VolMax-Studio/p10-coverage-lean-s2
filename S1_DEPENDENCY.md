# S1 dependency (single source of truth)

S2 depends on the **frozen, human-ratified S1 release tag**. The peeled commit is recorded for
reproducibility only.

```
repo:                   VolMax-Studio/p10-underdetermination-lean-s1
kind:                   tag
tag:                    v0.1.0-s1-ratified
tag object:             7c3df437de454466b932a5d0dc889b3287c64e05
peeled commit:          e4db3747eaeeb1a07227bb9029f9a9c3b566cdb1
git tree:               6cdf48c29cd2207243912881c8f38c416ba2026a
verifier manifest SHA-256: 06bf9129bf480c79ed5281ec2e944ac5613d1c340552ce5a415f5bf4c8965907
status:                 RATIFIED / FROZEN S1
```

- **The tag is immutable.** S2 depends on the tag `v0.1.0-s1-ratified`; the tag object, commit and
  tree are recorded so the dependency can be checked. If the tag ever resolved to another object,
  the dependency is broken and must not be silently re-pinned.
- S1 is ratified by a human act. S2a is ratified at `v0.1.0-s2a-ratified`.
- **How the dependency is realised.** `lakefile.toml` has one `[[require]]`, a `path` dependency on
  `vendor/p10-underdetermination-lean-s1/`, a byte-for-byte copy of the tag's tree (git tree id
  above). S1 is public; the vendored byte-for-byte copy is retained so S2a remains
  offline-reproducible and bound to the exact ratified S1 tree rather than mutable repository state.
  A `git` dependency is therefore not required. `scripts/s2a.py s1-identity` (part of the acceptance
  command) verifies the copy against S1's own `SHA256SUMS`, the pinned manifest digest and the git
  tree id. S1 semantics are not redefined; nothing in the vendored tree is edited.
- Toolchain mirrored from S1: `leanprover/lean4:v4.33.0` (conda-forge `lean4 4.33.0 build
  h6c1889d_0`; `lean` executable SHA-256 `9842f89b…`, identical to S1's pin); `autoImplicit = false`.
- Only these S1 modules are imported by the checker: `P10.Bound` (and transitively `P10.Wire`,
  `P10.Fixtures`, `P10.Core`, `P10.Certificate`, `P10.Sha256`, `P10.Bytes`).
