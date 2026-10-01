import P10S2.Codec
import P10.Wire

/-!
# P10S2.ProfileArtifact — `ProfileArtifactS2V0` (prereg §6a), strict canonical JSON

Canonical JSON in the style of frozen S1's wire format: a flat object, keys in sorted
(JCS) order, string values over `[A-Za-z0-9_.:-]` (no escapes, no whitespace), plus the
nested `key_resolution` object whose keys are strictly ascending. The decoder accepts
exactly one shape: a missing, extra, duplicated, reordered or otherwise non-canonical
field is a decode failure. General laws: `decode_encode_profile`, `encode_decode_profile`.

The four constant fields (`artifact_version`, `leaf_encoding`, `log_identity_scheme`,
`subject_derivation`) are part of the literal skeleton; any other value fails to decode.
Arrays (`authorized_admitters`) are strictly ascending, hence duplicate-free (prereg v0.2.5 §6a).
`pB` is an INPUT to the checker. No module of the checker library embeds a concrete `pB`.
-/

namespace P10S2
open Codec

/-- Token alphabet of S1: `[A-Za-z0-9_.:-]`. -/
def allTokB : Bytes → Bool
  | [] => true
  | n :: ns => P10.Wire.isTokChar n && allTokB ns

def readTok : Bytes → Option (Bytes × Bytes)
  | [] => none
  | c :: cs =>
    if c = 34 then some ([], cs)
    else if P10.Wire.isTokChar c = true then (readTok cs).map fun tr => (c :: tr.1, tr.2)
    else none

theorem readTok_append : ∀ (t r : Bytes), allTokB t = true → readTok (t ++ 34 :: r) = some (t, r)
  | [], r, _ => by simp [readTok]
  | a :: as, r, h => by
    simp only [allTokB, Bool.and_eq_true] at h
    obtain ⟨ha, has⟩ := h
    have hne : a ≠ 34 := by
      intro e
      subst e
      revert ha
      decide
    simp [readTok, hne, ha, readTok_append as r has]

theorem readTok_inv : ∀ (b t r : Bytes), readTok b = some (t, r) →
    allTokB t = true ∧ b = t ++ 34 :: r
  | [], _, _, h => by simp [readTok] at h
  | c :: cs, t, r, h => by
    unfold readTok at h
    by_cases h1 : c = 34
    · simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ht, hr⟩ := h
      subst ht; subst hr
      simp [allTokB, h1]
    · by_cases h2 : P10.Wire.isTokChar c = true
      · simp only [h1, h2, if_false, if_true] at h
        cases hc : readTok cs with
        | none => rw [hc] at h; simp at h
        | some tr =>
          rw [hc] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ht, hr⟩ := h
          subst ht; subst hr
          obtain ⟨ih1, ih2⟩ := readTok_inv cs tr.1 tr.2 hc
          refine ⟨by simp [allTokB, h2, ih1], ?_⟩
          simp [ih2]
      · simp only [h1, h2, if_false] at h
        simp at h

/-- A JSON string token (S1 alphabet), followed by its closing quote. -/
abbrev Tok := {b : Bytes // allTokB b = true}

def tokC : Codec Tok where
  enc t := t.1 ++ [34]
  dec b := (readTok b).bind fun tr =>
    if h : allTokB tr.1 = true then some (⟨tr.1, h⟩, tr.2) else none
  rt := by
    intro t r
    obtain ⟨t, ht⟩ := t
    have e : (t ++ [34]) ++ r = t ++ 34 :: r := by simp
    simp [e, readTok_append t r ht, ht]
  eq := by
    intro b t r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨t', r1⟩, hr, hc⟩ := h
    by_cases hp : allTokB t' = true
    · simp only [hp, dite_true, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨ht, hr2⟩ := hc
      subst hr2
      obtain ⟨_, hb⟩ := readTok_inv b t' r1 hr
      rw [hb, ← ht]
      simp
    · simp only [hp] at hc
      simp at hc

/-! ### Lexicographic order on byte strings (strictly ascending keys ⇒ unique, canonical) -/

def ltBytes : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if a = b then ltBytes as bs else false

def strictAscKeys : List (Tok × Tok) → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => ltBytes x.1.1 y.1.1 && strictAscKeys (y :: rest)

def strictAscToks : List Tok → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => ltBytes x.1 y.1 && strictAscToks (y :: rest)

/-! ### Container body: entries separated by `,`, closed by `term` (empty container = `term`)
(`term = 125` for objects, `93` for arrays) -/

def tailEnc {α : Type} (E : Codec α) (term : Nat) : List α → Bytes
  | [] => [term]
  | x :: xs => 44 :: (E.enc x ++ tailEnc E term xs)

def decTail {α : Type} (E : Codec α) (term : Nat) : Nat → Bytes → Option (List α × Bytes)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: r =>
    if c = term then some ([], r)
    else if c = 44 then (E.dec r).bind fun xr =>
      (decTail E term f xr.2).map fun lr => (xr.1 :: lr.1, lr.2)
    else none

theorem tailEnc_len_pos {α : Type} (E : Codec α) (term : Nat) (l : List α) :
    1 ≤ (tailEnc E term l).length := by
  cases l <;> simp [tailEnc]

theorem decTail_rt {α : Type} (E : Codec α) (term : Nat) (hterm : term ≠ 44) :
    ∀ (l : List α) (r : Bytes) (f : Nat), (tailEnc E term l).length ≤ f →
      decTail E term f (tailEnc E term l ++ r) = some (l, r)
  | [], r, f, h => by
    cases f with
    | zero => simp [tailEnc] at h
    | succ f => simp [tailEnc, decTail]
  | x :: xs, r, f, h => by
    cases f with
    | zero => simp [tailEnc] at h
    | succ f =>
      have h' : (E.enc x ++ tailEnc E term xs).length ≤ f := by
        simp only [tailEnc, List.length_cons] at h
        omega
      have hxs : (tailEnc E term xs).length ≤ f := by
        simp only [List.length_append] at h'
        omega
      have ih := decTail_rt E term hterm xs r f hxs
      have hne : ¬ (44 = term) := fun e => hterm e.symm
      simp only [tailEnc, List.cons_append, List.append_assoc, decTail]
      simp [hne, E.rt, ih]

theorem decTail_eq {α : Type} (E : Codec α) (term : Nat) :
    ∀ (f : Nat) (b : Bytes) (l : List α) (r : Bytes),
      decTail E term f b = some (l, r) → b = tailEnc E term l ++ r
  | 0, b, l, r, h => by simp [decTail] at h
  | f + 1, [], l, r, h => by simp [decTail] at h
  | f + 1, c :: b, l, r, h => by
    unfold decTail at h
    by_cases h1 : c = term
    · rw [if_pos h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hr⟩ := h
      subst hl; subst hr
      simp [tailEnc, h1]
    · by_cases h2 : c = 44
      · rw [if_neg h1, if_pos h2] at h
        cases hx : E.dec b with
        | none => rw [hx] at h; simp at h
        | some xr =>
          rw [hx] at h
          simp only [Option.bind_some] at h
          cases hL : decTail E term f xr.2 with
          | none => rw [hL] at h; simp at h
          | some lr =>
            rw [hL] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hl, hr⟩ := h
            subst hl; subst hr
            have e1 := E.eq _ _ _ hx
            have e2 := decTail_eq E term f _ _ _ hL
            simp only [tailEnc, List.cons_append, List.append_assoc]
            rw [h2, e1, e2]
      · rw [if_neg h1, if_neg h2] at h
        simp at h

/-- JSON-style container body. `hfirst`: every entry starts with `"` (never with `term`). -/
def objBody {α : Type} (E : Codec α) (term : Nat) (hterm : term ≠ 44) (h34 : term ≠ 34)
    (hfirst : ∀ a, ∃ t, E.enc a = 34 :: t) : Codec (List α) where
  enc
    | [] => [term]
    | x :: xs => E.enc x ++ tailEnc E term xs
  dec b :=
    if b.head? = some term then some ([], b.tail)
    else (E.dec b).bind fun xr =>
      (decTail E term b.length xr.2).map fun lr => (xr.1 :: lr.1, lr.2)
  rt := by
    intro l r
    cases l with
    | nil => simp
    | cons x xs =>
      obtain ⟨t, ht⟩ := hfirst x
      have hb : (E.enc x ++ tailEnc E term xs) ++ r = 34 :: (t ++ tailEnc E term xs ++ r) := by
        rw [ht]; simp
      have hne : ¬ ((E.enc x ++ tailEnc E term xs) ++ r).head? = some term := by
        rw [hb]
        simp only [List.head?_cons, Option.some.injEq]
        exact fun h => h34 h.symm
      have hl : (tailEnc E term xs).length ≤ ((E.enc x ++ tailEnc E term xs) ++ r).length := by
        simp only [List.length_append]; omega
      simp only [hne, if_false]
      rw [List.append_assoc, E.rt]
      have hl' : (tailEnc E term xs).length ≤ (E.enc x ++ (tailEnc E term xs ++ r)).length := by
        simp only [List.length_append]; omega
      simp only [Option.bind_some]
      rw [decTail_rt E term hterm xs r _ hl']
      rfl
  eq := by
    intro b l r h
    by_cases hh : b.head? = some term
    · simp only [hh, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hr⟩ := h
      subst hl; subst hr
      cases b with
      | nil => simp at hh
      | cons c cs =>
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp
    · simp only [hh, if_false] at h
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨x, r1⟩, hx, ⟨xs, r2⟩, hL, hl, hr⟩ := h
      subst hr
      subst hl
      have e1 := E.eq _ _ _ hx
      have e2 := decTail_eq E term _ _ _ _ hL
      simp only at e1 e2
      simp [e1, e2, List.append_assoc]

/-! ### The key-resolution object, the admitter array, and the artifact -/

def entryC : Codec (Tok × Tok) := pre [34] (prod tokC (pre [58, 34] tokC))

theorem entryC_first : ∀ a, ∃ t, entryC.enc a = 34 :: t := by
  intro a
  exact ⟨_, rfl⟩

/-- `KeyResolutionV0`: `iss` ↦ key fingerprint for the `iss` values whose frozen verification-key
material is available, keys strictly ascending. Membership grants NO authorization (prereg TB4). -/
abbrev KeyResolution := {es : List (Tok × Tok) // strictAscKeys es = true}

def keyResolutionC : Codec KeyResolution :=
  subtype strictAscKeys
    (pre [123] (objBody entryC 125 (by decide) (by decide) entryC_first))

def elemC : Codec Tok := pre [34] tokC

theorem elemC_first : ∀ a, ∃ t, elemC.enc a = 34 :: t := by
  intro a
  exact ⟨_, rfl⟩

/-- Explicit authorized admitter `iss` set (prereg v0.2.5 §6a): strictly ascending array. -/
abbrev AuthorizedAdmitters := {l : List Tok // strictAscToks l = true}

def authorizedAdmittersC : Codec AuthorizedAdmitters :=
  subtype strictAscToks (pre [91] (objBody elemC 93 (by decide) (by decide) elemC_first))

structure ProfileArtifact where
  admissionRuleId        : Tok
  authorizedAdmitters    : AuthorizedAdmitters
  checkpointVds          : Tok
  coverageRuleId         : Tok
  evidenceScopeRuleId    : Tok
  fixtureId              : Tok
  keyResolution          : KeyResolution
  leafEncodingSpecDigest : Tok
  normativeProfileDigest : Tok
  s1ProfileToken         : Tok
  verifierManifestDigest : Tok
  verifierManifestRef    : Tok
  deriving DecidableEq

def profileArtifactC : Codec ProfileArtifact :=
  iso
    (pre (bytes% "{\"admission_rule_id\":\"") <|
     prod tokC <|
     pre (bytes% ",\"artifact_version\":\"P10-S2-ProfileArtifact-v0\",\"authorized_admitters\":") <|
     prod authorizedAdmittersC <|
     pre (bytes% ",\"checkpoint_vds\":\"") <|
     prod tokC <|
     pre (bytes% ",\"coverage_rule_id\":\"") <|
     prod tokC <|
     pre (bytes% ",\"evidence_scope_rule_id\":\"") <|
     prod tokC <|
     pre (bytes% ",\"fixture_id\":\"") <|
     prod tokC <|
     pre (bytes% ",\"key_resolution\":") <|
     prod keyResolutionC <|
     pre (bytes% ",\"leaf_encoding\":\"LeafEncodeV0\",\"leaf_encoding_spec_digest\":\"") <|
     prod tokC <|
     pre (bytes% ",\"log_identity_scheme\":\"LogIdentityV0\",\"normative_profile_digest\":\"") <|
     prod tokC <|
     pre (bytes% ",\"s1_profile_token\":\"") <|
     prod tokC <|
     pre (bytes% ",\"subject_derivation\":\"SubjectDeriveV0\",\"verifier_manifest_digest\":\"") <|
     prod tokC <|
     pre (bytes% ",\"verifier_manifest_ref\":\"") <|
     post (bytes% "}") tokC)
    (fun p => (p.admissionRuleId, p.authorizedAdmitters, p.checkpointVds, p.coverageRuleId,
      p.evidenceScopeRuleId, p.fixtureId, p.keyResolution, p.leafEncodingSpecDigest,
      p.normativeProfileDigest, p.s1ProfileToken, p.verifierManifestDigest,
      p.verifierManifestRef))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl) (fun _ => rfl)

def encodeProfileArtifact (p : ProfileArtifact) : Bytes := profileArtifactC.enc p

def decodeProfileArtifact (b : Bytes) : Option ProfileArtifact := profileArtifactC.decodeAll b

/-- `decode ∘ encode = id` on every profile artifact. -/
theorem decode_encode_profile (p : ProfileArtifact) :
    decodeProfileArtifact (encodeProfileArtifact p) = some p :=
  Codec.decodeAll_enc _ p

/-- `encode ∘ decode = id` on every byte string that decodes (non-malleability of `pB`). -/
theorem encode_decode_profile (b : Bytes) (p : ProfileArtifact)
    (h : decodeProfileArtifact b = some p) : encodeProfileArtifact p = b :=
  Codec.enc_decodeAll _ b p h

end P10S2
