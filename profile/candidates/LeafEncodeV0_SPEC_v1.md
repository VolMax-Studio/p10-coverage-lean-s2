# LeafEncodeV0 — Specification v1

**Status:** v1. The wrapper mapping of §2 is the mapping selected by the project owner for this P10 instance. The exact raw bytes of this file are hashed with `LeafEncodeSpecArtifactDigestV0` (S2 prereg §6b) to produce `pB.leaf_encoding_spec_digest`.
**Profile basis:** P10 Underdetermination Profile v0.1.1 §2.4: "`LeafEncodeV0(x)` := frozen mapping from the exact registered Signed Statement bytes and their format/media-type identifier to RFC9162 leaf input". VDS: `RFC9162_SHA256` (COSE Receipts VDS `1`).
**Replaces:** the placeholder spec bound at S2 HEAD `fbcfefa` (artifact digest `b9a8602f…`).

## 1. Input

- `statement_bytes`: the exact byte string of the COSE_Sign1 Signed Statement **as submitted for registration**. No re-encoding, no CBOR tag added or removed, no change to protected or unprotected headers. In particular, any form to which a Transparency Service has added a Receipt (unprotected header label `394`) is **not** the input. Length ≥ 1.
- `format_id`: exactly the 32 ASCII bytes `application/scitt-statement+cose`. This is the only admissible value in v1. No case folding, parameters, aliases, or whitespace are allowed. Any other value means the statement is outside this profile instance.

## 2. Mapping

```text
leaf_input := "P10-LeafEncodeV0" || 0x00              -- 17 bytes, fixed
           || uint32_be(len(format_id))               -- always 0x00000020 in v1
           || format_id                               -- 32 bytes, fixed in v1
           || uint64_be(len(statement_bytes))         -- 1 ≤ len < 2^64
           || statement_bytes

leaf_hash  := SHA-256(0x00 || leaf_input)             -- RFC 9162 MTH({d0})
```

A decoder MUST consume `leaf_input` exactly: a wrong prefix, a length field that does not match the remaining bytes, trailing bytes, or `format_id` ≠ the v1 value → not a `LeafEncodeV0` leaf.

## 3. Log conformance precondition

`LeafEncodeV0` describes what the log *does*, not what P10 would like it to do. A Transparency Service is admissible for this profile instance only if, for every registered Signed Statement, the RFC 9162 leaf input it hashes equals `leaf_input` above. A service that hashes anything else (raw statement bytes, its own envelope, a receipt-bearing form, or a non-RFC 9162 VDS) is outside the instance. `FullPrefixReplay` against it yields REJECT under the profile's other-log rule.

Consequence: a third-party RFC 9162 service will almost certainly not use this P10 envelope. In practice, choosing this envelope means S3 uses a log whose leaf format P10 defines (self-hosted or contracted).

## 4. Adversarial notes (for the reviewer)

- **Injectivity.** The prefix is fixed, and in v1 `format_id` and its length are fixed. The `uint64` length is followed by exactly that many bytes with nothing after. Hence `leaf_input` ↦ `statement_bytes` is a bijection onto valid inputs. Two different `(format_id, statement_bytes)` pairs cannot collide at the byte level.
- **Domain separation.** The prefix keeps P10 leaves distinct from any other leaf format in a shared RFC 9162 log. The 0x00 RFC 9162 leaf prefix separates leaves from interior nodes.
- **Tagged vs untagged COSE.** These are different byte strings and yield different leaves (vectors L3/L4). There is no normalization. The issuer and the log must agree on the exact submitted bytes.
- **Receipt contamination.** Hashing the Transparent Statement instead of the Signed Statement would make the leaf depend on the receipt, which itself depends on the tree, which is circular. §1 forbids it.
- **TB3 note, not part of the mapping.** If VolMax both issues statements and operates the log, the non-equivocation assumption (S2 TB3) rests on the party with the omission incentive. That is admissible but weak. Witness cosigning or an independent operator strengthens it. This is a deployment decision for S3.
- **Alternative rejected for v1.** Identity mapping (`leaf_input := statement_bytes`) would interoperate with more generic logs, but it carries no P10 domain separation and does not bind `format_id` into the leaf. The project owner rejected it for this instance; it is recorded here for the decision record.

## 5. Normative test vectors

Inputs below are byte strings, not necessarily valid COSE. The mapping is bytes → bytes. `P = 5031302d4c656166456e636f646556300000000020` (prefix ‖ uint32 length), `F = 6170706c69636174696f6e2f73636974742d73746174656d656e742b636f7365` (`format_id`).

| ID | `statement_bytes` (hex) | `leaf_input` (hex) | `leaf_hash` |
|---|---|---|---|
| L1 | `00` | `P ‖ F ‖ 0000000000000001 ‖ 00` | `aa263d9ac89b59f1593d4eaf715d386e2b97d66efd91cead42818ad6978b1eb1` |
| L2 | `d2` | `P ‖ F ‖ 0000000000000001 ‖ d2` | `fc47e9bd265fe22b7c10d675c08a58debfab6077df8fd07dd5eb4eb1162c3eba` |
| L3 | `d28440a0f640` (tagged skeleton) | `P ‖ F ‖ 0000000000000006 ‖ d28440a0f640` | `1b0beaae426397b4679962a774ac4fa48437fd18b1a2e89e881944a6fadd2131` |
| L4 | `8440a0f640` (untagged skeleton) | `P ‖ F ‖ 0000000000000005 ‖ 8440a0f640` | `2531f8eb6c09b3b7b1ba438b1d39fa734495cbb4a65b30c5090e6935253f884b` |
| L5 | bytes `00 01 … ff` (256 bytes) | `P ‖ F ‖ 0000000000000100 ‖ 00…ff` (317 bytes) | `0662f02bffb4f14934debd070b0670a425b31cff9b2fb70192ca7eca7cd48a54` |
| L6 | empty | — | not encodable (length ≥ 1) |
| L7 | `00`, but `format_id = APPLICATION/SCITT-STATEMENT+COSE` | — | not encodable (only the exact v1 identifier) |
| L8 | `leaf_input` of L1 with one trailing byte appended | — | decode failure (trailing bytes) |

Full `leaf_input` for L1:
`5031302d4c656166456e636f6465563000000000206170706c69636174696f6e2f73636974742d73746174656d656e742b636f7365000000000000000100`
