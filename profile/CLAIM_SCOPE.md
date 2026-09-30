# Claim scope (DRAFT — not ratified)

If S2 is ever proven, it will establish, relative to a frozen instance
commitment and a checkpoint-bound authenticated transcript through `S_R`, that
the evidence bundle supplied to S1 is exactly the bundle constructed from every
valid in-scope `RelevantAdmission` visible in the committed prefix.

It will **not** establish: that all evidence in the world was registered;
that the selected log contains all relevant evidence; that no sibling
instance exists; that an issuer was ignorant of unregistered/out-of-scope
evidence; global non-equivocation of the Transparency Service; or anything
about registrations after `S_R`.

**Consistency vs adequacy.** Coverage is consistency/completeness relative to a
frozen authorization policy, relevance predicate, evidence scope, admission
rules and key-resolution policy. It does not prove those policies adequately
describe all real-world evidence that could change the verdict.

Nothing in this repository currently proves any of the above.
