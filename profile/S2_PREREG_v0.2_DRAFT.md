# P10 S2 — Coverage / Evidence-Closure Preregistration v0.2

**DRAFT — NOT RATIFIED.** Not human-signed. This file is a delta register,
not the finished v0.2 text. The v0.1 candidate text (dated 2026-09-30) remains
the baseline; it is not reproduced here. The owner must author the integrated
v0.2 text; nothing below settles semantics.

S1 dependency: frozen, human-ratified tag `v0.1.0-s1-ratified` (see
`../S1_DEPENDENCY.md`). S1 is ratified; this S2 draft is not.

## Mandatory v0.2 changes (from the two text-only gates) — OPEN

| # | Change | Gate refs | Status |
|---|--------|-----------|--------|
| 1 | Faithful `Bundle` law (single-item faithfulness, permutation invariance for fixture, refinement monotonicity, explicit conflict semantics; total on `[]` and conflicting items) | F-S2-1 | text open |
| 2 | Exact S2→S1 evidence-byte binding (coverage-produced evidence == evidence decoded from S1 instance bytes); S2-N0 must fail against the composition theorem itself | B1, F-S2-2 | text open |
| 3 | Checkpoint-bound transcript: log identity, size, root, `S_R`; `CoverageSpec` quantifies over indices `< size(S_R)`; full-prefix completeness premise named explicitly | B2, F-S2-6 | text open |
| 4 | Authorization/relevance decided in Lean; S2b supplies typed status (`valid | badSignature | payloadUnavailable`), not a filtered view | B3 | text open |
| 5 | TB6 closure/adjudication timing and `S_R` selection; no claim after `S_R`; no freshness | F-S2-4 | text open |
| 6 | Adequacy limitation: policy/scope/relevance correctness is not a Lean theorem; re-scope S2-N0 to "registered, in-policy omission" | F-S2-3 | text open |

## Smaller items — OPEN

- zero closures → HALT; ≥2 valid owner closures → REJECT
- M29 `checkpoint_preclosure_transcript_digest` rule
- profile commitment registered before first admission; non-owner lifecycle entry → REJECT
- align §1 claim-of-record with §7/§16 (incl. post-closure-through-`S_R`; "registered" vs "in committed prefix", F-S2-5)
- HALT invariant at type level and on the composed verdict function
- canonical transcript and bundle theorems (decode/encode uniqueness)
- reconcile §5.1 vs TB4 key time-scoping (F-S2-9)
- optional: one summary row per leaf in `[0, size(S_R))` (TCB reduction; state scale limits)
- S2b gate: differential second classifier for `SubjectView` extraction
- new negatives N11–N14 (see `../tests/planned/`)
