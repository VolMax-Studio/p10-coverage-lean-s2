import P10S2.ProfileArtifact
import P10.Sha256
import P10.Wire

/-!
# P10S2.Digests — the canonical digests of prereg v0.2.5 §6b

All structured digests are SHA-256 over JCS (RFC 8785) bytes. In S2 v0 every string value is
restricted to the S1 token alphabet `[A-Za-z0-9_.:-]` or lowercase hex, so the JCS output is the
literal skeleton with sorted keys, no whitespace and no escapes; the bytes are built directly.
`LeafEncodeSpecArtifactDigestV0` is the binary-artifact exception (profile §2.7): SHA-256 over
fixed prefixes and the exact raw file bytes, with no JCS layer.
-/

namespace P10S2
open P10.Sha256 (sha256)

/-! ### Byte-string helpers -/

def hexDigit (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

/-- Lowercase hex of one byte. -/
def hexByte (n : Nat) : Bytes := [hexDigit (n / 16 % 16), hexDigit (n % 16)]

def hexOf : Bytes → Bytes
  | [] => []
  | b :: bs => hexByte b ++ hexOf bs

def decDigits : Nat → Nat → Bytes
  | 0, _ => []
  | f + 1, n => if n < 10 then [48 + n] else decDigits f (n / 10) ++ [48 + n % 10]

/-- Canonical decimal string of a natural number. -/
def natDec (n : Nat) : Bytes := decDigits (n + 1) n

/-- JSON string: `"s"` (no escapes are ever needed for token-alphabet strings). -/
def q (s : Bytes) : Bytes := 34 :: (s ++ [34])

def joinComma : List Bytes → Bytes
  | [] => []
  | [x] => x
  | x :: y :: r => x ++ 44 :: joinComma (y :: r)

/-- JSON array of already-serialized items. -/
def arr (xs : List Bytes) : Bytes := 91 :: (joinComma xs ++ [93])

/-! ### The digests of §6b -/

/-- `ClaimDigestV0(c) = SHA-256(JCS({"claim": claimTok c}))`. -/
def claimDigestV0 (c : P10.S1.Claim) : Digest :=
  ⟨sha256 (bytes% "{\"claim\":" ++ q (P10.Wire.claimTok c) ++ [125])⟩

/-- `EvidenceDigestV0(e) = SHA-256(JCS({"evidence": evidenceTok e}))`, for the S1 token `tok`. -/
def evidenceDigestV0 (tok : Bytes) : Digest :=
  ⟨sha256 (bytes% "{\"evidence\":" ++ q tok ++ [125])⟩

/-- `AuthorizedAdmittersDigestV0(A)`, `A` strictly ascending. -/
def authorizedAdmittersDigestV0 (a : List Bytes) : Digest :=
  ⟨sha256 (bytes% "{\"authorized_admitters\":" ++ arr (a.map q) ++ [125])⟩

/-- `KeyResolutionDigestV0(K) = SHA-256(JCS({"key_resolution": K}))`, `K` in `pB` canonical form. -/
def keyResolutionDigestV0 (kr : KeyResolution) : Digest :=
  ⟨sha256 (bytes% "{\"key_resolution\":" ++ keyResolutionC.enc kr ++ [125])⟩

/-- Normative JCS token of a statement kind inside `PreclosureDigestV0` (prereg v0.2.6 kind-token
table, K-1): the hashed string is this token, never the constructor name. -/
def kindTok : Kind → Bytes
  | .profileCommit => bytes% "profile_commit"
  | .instanceCommit => bytes% "instance_commit"
  | .admission => bytes% "admission"
  | .closure => bytes% "closure"
  | .adjudication => bytes% "adjudication"

/-- `PreclosureDigestV0(v)`: `{"preclosure_view": [[idx, kind, iss], …]}`, `idx` a canonical
decimal string, in leaf order. -/
def preclosureDigestV0 (v : List (Nat × Kind × Iss)) : Digest :=
  ⟨sha256 (bytes% "{\"preclosure_view\":" ++
    arr (v.map fun e => arr [q (natDec e.1), q (kindTok e.2.1), q e.2.2.bytes]) ++ [125])⟩

/-- The JCS input of `SubjectDeriveV0`. -/
def subjectDeriveInput (i r : Bytes) : Bytes :=
  bytes% "{\"issuer_id\":" ++ q i ++ bytes% ",\"request_id\":" ++ q (hexOf r) ++
    bytes% ",\"v\":\"SubjectDeriveV0\"}"

/-- `SubjectDeriveV0(i, r) = "p10s2sub:" ++ hex(SHA-256(JCS({"issuer_id": i,
"request_id": hex(r), "v": "SubjectDeriveV0"})))`, a `tstr`. -/
def subjectDeriveV0 (i : Iss) (r : Bytes) : Subject :=
  ⟨bytes% "p10s2sub:" ++ hexOf (sha256 (subjectDeriveInput i.bytes r))⟩

/-- `{"rule": R, "verifier_manifest_digest": M}` descriptor digest. -/
def ruleDigest (rule md : Bytes) : Digest :=
  ⟨sha256 (bytes% "{\"rule\":" ++ q rule ++ bytes% ",\"verifier_manifest_digest\":" ++ q md ++
    [125])⟩

def subjectDerivationDigestV0 (p : ProfileArtifact) : Digest :=
  ruleDigest (bytes% "SubjectDeriveV0") p.verifierManifestDigest.1

def evidenceScopeDigestV0 (p : ProfileArtifact) : Digest :=
  ruleDigest p.evidenceScopeRuleId.1 p.verifierManifestDigest.1

def admissionRuleDigestV0 (p : ProfileArtifact) : Digest :=
  ruleDigest p.admissionRuleId.1 p.verifierManifestDigest.1

def coverageRuleDigestV0 (p : ProfileArtifact) : Digest :=
  ruleDigest p.coverageRuleId.1 p.verifierManifestDigest.1

/-- `LeafEncodingProfileDigestV0 = SHA-256(JCS({"rule": "LeafEncodeV0",
"spec_digest": pB.leaf_encoding_spec_digest}))`. -/
def leafEncodingProfileDigestV0 (p : ProfileArtifact) : Digest :=
  ⟨sha256 (bytes% "{\"rule\":\"LeafEncodeV0\",\"spec_digest\":" ++
    q p.leafEncodingSpecDigest.1 ++ [125])⟩

/-- **`LeafEncodeSpecArtifactDigestV0(f)`** (prereg v0.2.5 G6-B3), NOT JCS:
`SHA-256("P10-LeafEncodeSpecArtifact-v0:" ++ "text-markdown-utf-8-v0:" ++ f)`, `f` = exact raw file bytes. -/
def leafEncodeSpecArtifactDigestV0 (f : Bytes) : Digest :=
  ⟨sha256 (bytes% "P10-LeafEncodeSpecArtifact-v0:" ++ bytes% "text-markdown-utf-8-v0:" ++ f)⟩

/-- The explicit admitter set of a profile artifact, as `iss` values. -/
def admitterIss (p : ProfileArtifact) : List Iss := p.authorizedAdmitters.1.map fun t => ⟨t.1⟩

/-- Its digest input: the `iss` strings, in the artifact's (ascending) order. -/
def authorizedAdmittersDigestOf (p : ProfileArtifact) : Digest :=
  authorizedAdmittersDigestV0 (p.authorizedAdmitters.1.map fun t => t.1)

end P10S2
