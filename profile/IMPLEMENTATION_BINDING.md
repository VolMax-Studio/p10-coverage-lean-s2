# S2a / S2b interface binding (DRAFT — not ratified)

Lean (S2a) receives, per transcript: the checkpoint `(logId, size, root)`;
a summary row `(idx, sub)` for every leaf in `[0, size)`; and a `RawEntry`
(`idx, iss, sub, claimedKind, payload bytes, sigStatus`) for every
matching-subject leaf — including badly signed and payload-unavailable ones.

S2b's residual obligations: row `i`'s `sub` is leaf `i`'s protected `sub`;
root reconstruction equals the checkpoint root; `sigStatus` is correct under
the frozen key map; bytes are the registered bytes. S2b acceptance must
include a differential second classifier.

Lean decides: authorization, scope, relevance, lifecycle validity, closure
validity, REJECT vs HALT, bundle construction, S1 byte binding.

Canonical transcript bytes and the exact byte-binding to the checked
proposition are open (v0.2 items).
