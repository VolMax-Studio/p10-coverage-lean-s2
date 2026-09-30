# LeafEncodeV0 (S2a implementation-authored spec artifact)

Status: authored by the S2a implementation because prereg v0.2.5 requires a frozen,
manifest-covered `LeafEncodeV0` spec file but supplies no content (reported as a prereg gap).

A log leaf is the UTF-8 byte string of one canonical row: the JCS object
`{"iss":I,"kind":K,"payload":P,"sig":S,"sub":U}` restricted to the S1 token alphabet.
S2a does not execute LeafEncodeV0; S2b owns execution conformance. S2a only binds this
file's digest via `pB.leaf_encoding_spec_digest`.
