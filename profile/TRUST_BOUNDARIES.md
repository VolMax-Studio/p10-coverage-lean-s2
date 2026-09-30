# Trust boundaries (DRAFT — not ratified)

- **TB0** Lean kernel/toolchain — inherited from S1, pinned (`lean-toolchain`).
- **TB1** S1 semantics — S2 must not redefine `CertificateTargetV0`,
  `Underdetermined`, `Compatible`, `Eval`, `Wπ`, `Eπ`.
- **TB2** Authenticated transcript producer (S2b): COSE verification, payload
  parsing, frozen key lookup, prefix replay, checkpoint verification, leaf
  summaries. S2b attests *facts*; it must not decide authorization,
  relevance, scope or closure validity, and must not drop entries.
- **TB3** Transparency Service: checkpoint authenticity and VDS ordering are
  assumed/externally verified, never promoted to Lean-proven facts.
- **TB4** Identity/key resolution: frozen historical binding (digest in the
  commitment); dynamic resolution inadmissible.
- **TB5** Availability: missing leaf/header/payload ⇒ HALT, never evidence
  absence.
- **TB6 (reserved)** Closure/adjudication timing and selection of `S_R`. S2
  claims completeness only through the committed `S_R`; nothing about later
  registrations; no freshness guarantee unless the party with an omission
  incentive does not control `S_R`.

## Completeness premise (to be made explicit in v0.2)

"Authenticated" ≠ "complete subject view of the full prefix". Lean can only
conclude completeness through `S_R` if the transcript binds (log id, size,
root) and supplies coverage of every index in `[0, size(S_R))`.
