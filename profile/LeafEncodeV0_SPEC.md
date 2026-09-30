# LeafEncodeV0 — normative binding artifact (S2a)

Status: manifest-covered binding artifact. It fixes WHICH specification `pB.leaf_encoding_spec_digest`
commits to. It is not an executable encoder, and S2a does not execute it.

## Authoritative definition (frozen profile v0.1.1, §2.4, quoted)

    LeafEncodeV0(x) := frozen mapping from the exact registered Signed Statement
      bytes and their format/media-type identifier to RFC9162 leaf input

## Binding semantics

- Input `x`: the exact registered Signed Statement bytes, together with their format/media-type
  identifier. Nothing else is an input.
- Output: the RFC 9162 (SHA-256 VDS) leaf input, given by the frozen mapping above.
- `LeafEncodeV0` is defined on the registered statement bytes and their format/media-type
  identifier only. It is not defined from, and must not be reconstructed from, parsed P10 fields
  (`iss`, `kind`, `payload`, `sig`, `sub`) or from any re-serialized semantic row.

## What is and is not specified here

The frozen profile v0.1.1 and prereg v0.2.5 do not define a byte-level mapping from (statement
bytes, format/media-type identifier) to the RFC 9162 leaf input, nor a registry of identifiers.
This artifact does not invent one. Consequently:

- S2a's obligation is limited to the digest binding of this specification artifact:
  `pB.leaf_encoding_spec_digest = LeafEncodeSpecArtifactDigestV0(raw bytes of this file)`.
- S2a does not claim to execute SCITT/COSE leaf encoding, to recompute leaves, or to reconstruct
  the VDS root. Executable conformance of `LeafEncodeV0` is an S2b obligation and requires a
  normative decision fixing the concrete mapping and the format/media-type identifiers.
- `LeafEncodeV0` remains an explicit premise (TB2, `TranscriptFaithful`), never discharged in Lean.
