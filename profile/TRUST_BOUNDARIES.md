# Trust boundaries (S2a)

The authoritative statement is prereg v0.2.4 §4 (TB0–TB7). In this repository:

- **TB0** Lean kernel and toolchain: pinned `leanprover/lean4:v4.33.0` (conda-forge build
  `h6c1889d_0`; the `lean` executable digest is pinned in `scripts/s2a.py` and recorded in the
  verifier manifest).
- **TB1** S1 semantics: untouched; the frozen ratified tag is required (`S1_DEPENDENCY.md`).
- **TB2** Transcript producer (S2b, not authorized here): supplies observations only. Lean decides
  authorization, relevance, lifecycle validity, closure validity, REJECT vs HALT.
  `TranscriptFaithful T V` is the only premise linking `T` to the real log (`CoverageSpec.lean`).
- **TB3** Transparency service non-equivocation: assumed.
- **TB4** Key resolution: `KeyResolutionV0` lives in `pB`, bound by `profile_digest`;
  `authorized_admitter_set_digest` remains an `iss`-set digest (interpretation I-4).
- **TB5** Availability: any unavailable row / subject payload / authorized key → HALT; never
  evidence of absence.
- **TB6** Checkpoint selection and freshness: no claim about leaves at `idx ≥ size(S_R)`.
- **TB7** Verifier identity: `scripts/s2a.py tb7` (harness), not a Lean theorem.
