import P10S2.Types

/-!
# P10S2.Codec — strict, non-malleable codecs with the two general laws

A `Codec α` bundles an encoder, a *prefix* decoder (returns the unconsumed rest) and
the two canonicality laws for every value and every byte string:

* `rt` : `dec (enc a ++ r) = some (a, r)`                 (decode ∘ encode = id)
* `eq` : `dec b = some (a, r) → b = enc a ++ r`           (encode ∘ decode = id)

Combinators preserve both laws, so each concrete codec inherits them without a
per-vector check. Only structural recursion is used (kernel-evaluable).
-/

namespace P10S2

structure Codec (α : Type) where
  enc : α → Bytes
  dec : Bytes → Option (α × Bytes)
  rt  : ∀ a r, dec (enc a ++ r) = some (a, r)
  eq  : ∀ b a r, dec b = some (a, r) → b = enc a ++ r

namespace Codec

/-! ### Natural numbers: `n = 255·q + m` as `q` bytes `255` then the byte `m < 255`. -/

def encNat (n : Nat) : Bytes := List.replicate (n / 255) 255 ++ [n % 255]

def decNatAux : Nat → Bytes → Option (Nat × Bytes)
  | _, [] => none
  | acc, b :: bs =>
    if b < 255 then some (acc + b, bs)
    else if b = 255 then decNatAux (acc + 255) bs
    else none

theorem decNatAux_rep (q m : Nat) (hm : m < 255) (r : Bytes) :
    ∀ acc, decNatAux acc (List.replicate q 255 ++ m :: r) = some (acc + 255 * q + m, r) := by
  induction q with
  | zero => intro acc; simp [decNatAux, hm]
  | succ q ih =>
    intro acc
    have h := ih (acc + 255)
    simp only [List.replicate_succ, List.cons_append, decNatAux]
    simp only [Nat.lt_irrefl, if_false, if_true]
    rw [h]
    congr 2
    omega

theorem decNatAux_inv : ∀ (b : Bytes) (acc v : Nat) (r : Bytes),
    decNatAux acc b = some (v, r) →
    ∃ q m, m < 255 ∧ v = acc + 255 * q + m ∧ b = List.replicate q 255 ++ m :: r
  | [], _, _, _, h => by simp [decNatAux] at h
  | x :: xs, acc, v, r, h => by
    unfold decNatAux at h
    by_cases h1 : x < 255
    · simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst hv; subst hr
      exact ⟨0, x, h1, by omega, by simp⟩
    · by_cases h2 : x = 255
      · simp only [h2, if_true] at h
        obtain ⟨q, m, hm, hv, hb⟩ := decNatAux_inv xs (acc + 255) v r h
        refine ⟨q + 1, m, hm, by omega, ?_⟩
        rw [hb, h2]
        simp [List.replicate_succ]
      · simp only [h1, h2, if_false] at h
        exact absurd h (by simp)

def nat : Codec Nat where
  enc := encNat
  dec := decNatAux 0
  rt := by
    intro n r
    have h := decNatAux_rep (n / 255) (n % 255) (Nat.mod_lt _ (by omega)) r 0
    have e : encNat n ++ r = List.replicate (n / 255) 255 ++ (n % 255) :: r := by
      simp [encNat]
    rw [e, h]
    congr 2
    omega
  eq := by
    intro b n r h
    obtain ⟨q, m, hm, hv, hb⟩ := decNatAux_inv b 0 n r h
    have e1 : n / 255 = q := by omega
    have e2 : n % 255 = m := by omega
    rw [hb]
    simp [encNat, e1, e2]

/-! ### Combinators -/

def prod {α β : Type} (A : Codec α) (B : Codec β) : Codec (α × β) where
  enc p := A.enc p.1 ++ B.enc p.2
  dec b := (A.dec b).bind fun ar => (B.dec ar.2).map fun br => ((ar.1, br.1), br.2)
  rt := by
    intro p r
    obtain ⟨a, b⟩ := p
    simp [List.append_assoc, A.rt, B.rt]
  eq := by
    intro b p r h
    obtain ⟨a, b'⟩ := p
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨a', r1⟩, hA, ⟨b'', r2⟩, hB, hpr⟩ := h
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨⟨ha, hb⟩, hr⟩ := hpr
    subst ha; subst hb; subst hr
    have e1 := A.eq _ _ _ hA
    have e2 := B.eq _ _ _ hB
    simp only at e1 e2
    rw [e1, e2]
    simp [List.append_assoc]

/-- Transport along an isomorphism (structure ↔ tuple, etc.). -/
def iso {α β : Type} (B : Codec β) (e : α → β) (g : β → α)
    (h1 : ∀ a, g (e a) = a) (h2 : ∀ b, e (g b) = b) : Codec α where
  enc a := B.enc (e a)
  dec b := (B.dec b).map fun br => (g br.1, br.2)
  rt := by
    intro a r
    simp [B.rt, h1]
  eq := by
    intro b a r h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨x, r'⟩, hx, hpr⟩ := h
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨ha, hr⟩ := hpr
    subst hr
    have e1 := B.eq _ _ _ hx
    rw [e1, ← ha, h2]

/-- A literal prefix. -/
def pre {α : Type} (lit : Bytes) (A : Codec α) : Codec α where
  enc a := lit ++ A.enc a
  dec b := match lit, b with
    | _, b' => if lit.isPrefixOf b' then A.dec (b'.drop lit.length) else none
  rt := by
    intro a r
    have hp : lit.isPrefixOf (lit ++ (A.enc a ++ r)) = true := by simp
    simp only [List.append_assoc, hp, if_true]
    rw [List.drop_left]
    exact A.rt a r
  eq := by
    intro b a r h
    by_cases hp : lit.isPrefixOf b = true
    · simp only [hp, if_true] at h
      have e1 := A.eq _ _ _ h
      have hb : b = lit ++ b.drop lit.length := by
        have := List.isPrefixOf_iff_prefix.mp hp
        obtain ⟨t, ht⟩ := this
        rw [← ht]; simp
      rw [hb, e1]
      simp [List.append_assoc]
    · simp only [hp] at h
      simp at h

/-- A literal suffix. -/
def post {α : Type} (lit : Bytes) (A : Codec α) : Codec α where
  enc a := A.enc a ++ lit
  dec b := (A.dec b).bind fun ar =>
    if lit.isPrefixOf ar.2 then some (ar.1, ar.2.drop lit.length) else none
  rt := by
    intro a r
    have hp : lit.isPrefixOf (lit ++ r) = true := by simp
    simp [List.append_assoc, A.rt]
  eq := by
    intro b a r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨a', r1⟩, hA, hc⟩ := h
    by_cases hp : lit.isPrefixOf r1 = true
    · simp only [hp, if_true, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨ha, hr⟩ := hc
      subst ha
      have e1 := A.eq _ _ _ hA
      have hr1 : r1 = lit ++ r := by
        have := List.isPrefixOf_iff_prefix.mp hp
        obtain ⟨t, ht⟩ := this
        rw [← ht] at hr ⊢
        simp at hr
        rw [hr]
      rw [e1, hr1]
      simp [List.append_assoc]
    · simp only [hp] at hc
      simp at hc

/-- Subtype by a `Bool` predicate; the decoder enforces the predicate (strict). -/
def subtype {α : Type} (p : α → Bool) (A : Codec α) : Codec {a : α // p a = true} where
  enc a := A.enc a.1
  dec b := (A.dec b).bind fun ar =>
    if h : p ar.1 = true then some (⟨ar.1, h⟩, ar.2) else none
  rt := by
    intro a r
    obtain ⟨a, ha⟩ := a
    simp [A.rt, ha]
  eq := by
    intro b a r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨a', r1⟩, hA, hc⟩ := h
    by_cases hp : p a' = true
    · simp only [hp, dite_true, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨ha, hr⟩ := hc
      subst hr
      have e1 := A.eq _ _ _ hA
      rw [e1, ← ha]
    · simp only [hp] at hc
      simp at hc

/-! ### Count-prefixed lists -/

def decListN {α : Type} (A : Codec α) : Nat → Bytes → Option (List α × Bytes)
  | 0, b => some ([], b)
  | n + 1, b => (A.dec b).bind fun ar =>
      (decListN A n ar.2).map fun lr => (ar.1 :: lr.1, lr.2)

def encList {α : Type} (A : Codec α) : List α → Bytes
  | [] => []
  | a :: l => A.enc a ++ encList A l

theorem decListN_rt {α : Type} (A : Codec α) :
    ∀ (l : List α) (r : Bytes), decListN A l.length (encList A l ++ r) = some (l, r)
  | [], r => by simp [decListN, encList]
  | a :: l, r => by
    simp only [List.length_cons, decListN, encList, List.append_assoc, A.rt]
    simp [decListN_rt A l r]

theorem decListN_eq {α : Type} (A : Codec α) :
    ∀ (n : Nat) (b : Bytes) (l : List α) (r : Bytes),
      decListN A n b = some (l, r) → b = encList A l ++ r ∧ l.length = n
  | 0, b, l, r, h => by
    simp only [decListN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hr⟩ := h
    subst hl; subst hr
    simp [encList]
  | n + 1, b, l, r, h => by
    simp only [decListN, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, r1⟩, hA, ⟨l', r2⟩, hL, hpr⟩ := h
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨hl, hr⟩ := hpr
    subst hl; subst hr
    have e1 := A.eq _ _ _ hA
    obtain ⟨e2, hlen⟩ := decListN_eq A n r1 l' r2 hL
    refine ⟨?_, by simp [hlen]⟩
    rw [e1, e2]
    simp [encList, List.append_assoc]

def list {α : Type} (A : Codec α) : Codec (List α) where
  enc l := nat.enc l.length ++ encList A l
  dec b := (nat.dec b).bind fun nr => decListN A nr.1 nr.2
  rt := by
    intro l r
    simp only [List.append_assoc, nat.rt]
    simp [decListN_rt A l r]
  eq := by
    intro b l r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨n, r1⟩, hn, hL⟩ := h
    have e1 := nat.eq _ _ _ hn
    obtain ⟨e2, hlen⟩ := decListN_eq A n r1 l r hL
    rw [e1, e2, hlen]
    simp [List.append_assoc]

/-! ### Tagged sums and enumerations -/

/-- Enumeration via a natural-number tag. -/
def enum {α : Type} (toNat : α → Nat) (ofNat : Nat → Option α)
    (h1 : ∀ a, ofNat (toNat a) = some a) (h2 : ∀ n a, ofNat n = some a → n = toNat a) :
    Codec α where
  enc a := nat.enc (toNat a)
  dec b := (nat.dec b).bind fun nr => (ofNat nr.1).map fun a => (a, nr.2)
  rt := by
    intro a r
    simp [nat.rt, h1]
  eq := by
    intro b a r h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨n, r1⟩, hn, a', ha, hpr⟩ := h
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨ha', hr⟩ := hpr
    subst ha'; subst hr
    have e1 := nat.eq _ _ _ hn
    rw [e1, h2 n a' ha]

def bool : Codec Bool :=
  enum (fun b => if b then 1 else 0)
    (fun n => if n = 0 then some false else if n = 1 then some true else none)
    (by intro a; cases a <;> simp)
    (by
      intro n a h
      by_cases h0 : n = 0
      · simp [h0] at h; subst h; simp [h0]
      · by_cases h1 : n = 1
        · simp [h1] at h; subst h; simp [h1]
        · simp [h0, h1] at h)

def option {α : Type} (A : Codec α) : Codec (Option α) where
  enc
    | none => nat.enc 0
    | some a => nat.enc 1 ++ A.enc a
  dec b := (nat.dec b).bind fun nr =>
    if nr.1 = 0 then some (none, nr.2)
    else if nr.1 = 1 then (A.dec nr.2).map fun ar => (some ar.1, ar.2)
    else none
  rt := by
    intro o r
    cases o with
    | none =>
      show ((nat.dec (nat.enc 0 ++ r)).bind _) = _
      rw [nat.rt]
      simp
    | some a =>
      simp only [List.append_assoc, nat.rt]
      simp [A.rt]
  eq := by
    intro b o r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨n, r1⟩, hn, hc⟩ := h
    have e1 := nat.eq _ _ _ hn
    by_cases h0 : n = 0
    · simp only [h0, if_true, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨ho, hr⟩ := hc
      subst ho; subst hr
      rw [e1, h0]
    · by_cases h1 : n = 1
      · have hc' : (A.dec r1).map (fun ar => (some ar.1, ar.2)) = some (o, r) := by
          simpa [h0, h1] using hc
        cases hA : A.dec r1 with
        | none => rw [hA] at hc'; simp at hc'
        | some ar =>
          rw [hA] at hc'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨ho, hr⟩ := hc'
          subst ho; subst hr
          have e2 := A.eq _ _ _ hA
          rw [e1, h1, e2]
          simp [List.append_assoc]
      · simp only [h0, h1, if_false] at hc
        simp at hc

/-- Raw byte strings: count-prefixed, every element a natural number. -/
def bytes : Codec Bytes := list nat

/-- The trivial codec. -/
def unit : Codec Unit where
  enc _ := []
  dec b := some ((), b)
  rt := by intro a r; rfl
  eq := by
    intro b a r h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hr⟩ := h
    subst hr
    rfl

/-- Tagged binary sum: tag 0 then `A`, tag 1 then `B`. -/
def sum {α β : Type} (A : Codec α) (B : Codec β) : Codec (α ⊕ β) where
  enc
    | .inl a => nat.enc 0 ++ A.enc a
    | .inr b => nat.enc 1 ++ B.enc b
  dec b := (nat.dec b).bind fun nr =>
    if nr.1 = 0 then (A.dec nr.2).map fun ar => (Sum.inl ar.1, ar.2)
    else if nr.1 = 1 then (B.dec nr.2).map fun br => (Sum.inr br.1, br.2)
    else none
  rt := by
    intro x r
    cases x with
    | inl a =>
      show ((nat.dec (nat.enc 0 ++ A.enc a ++ r)).bind _) = _
      rw [List.append_assoc, nat.rt]
      simp [A.rt]
    | inr b =>
      show ((nat.dec (nat.enc 1 ++ B.enc b ++ r)).bind _) = _
      rw [List.append_assoc, nat.rt]
      simp [B.rt]
  eq := by
    intro b x r h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨n, r1⟩, hn, hc⟩ := h
    have e1 := nat.eq _ _ _ hn
    by_cases h0 : n = 0
    · have hc' : (A.dec r1).map (fun ar => (Sum.inl ar.1, ar.2)) = some (x, r) := by
        simpa [h0] using hc
      cases hA : A.dec r1 with
      | none => rw [hA] at hc'; simp at hc'
      | some ar =>
        rw [hA] at hc'
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc'
        obtain ⟨hx, hr⟩ := hc'
        subst hx; subst hr
        have e2 := A.eq _ _ _ hA
        rw [e1, h0, e2]
        simp [List.append_assoc]
    · by_cases h1 : n = 1
      · have hc' : (B.dec r1).map (fun br => (Sum.inr br.1, br.2)) = some (x, r) := by
          simpa [h0, h1] using hc
        cases hB : B.dec r1 with
        | none => rw [hB] at hc'; simp at hc'
        | some br =>
          rw [hB] at hc'
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc'
          obtain ⟨hx, hr⟩ := hc'
          subst hx; subst hr
          have e2 := B.eq _ _ _ hB
          rw [e1, h1, e2]
          simp [List.append_assoc]
      · simp [h0, h1] at hc

/-- Strict decoder: the whole input must be consumed. -/
def decodeAll {α : Type} (C : Codec α) (b : Bytes) : Option α :=
  match C.dec b with
  | some (a, []) => some a
  | _ => none

theorem decodeAll_enc {α : Type} (C : Codec α) (a : α) :
    C.decodeAll (C.enc a) = some a := by
  have h := C.rt a []
  rw [List.append_nil] at h
  simp [decodeAll, h]

theorem enc_decodeAll {α : Type} (C : Codec α) (b : Bytes) (a : α)
    (h : C.decodeAll b = some a) : C.enc a = b := by
  unfold decodeAll at h
  cases hd : C.dec b with
  | none => rw [hd] at h; simp at h
  | some ar =>
    obtain ⟨a', r⟩ := ar
    rw [hd] at h
    cases r with
    | nil =>
      simp only [Option.some.injEq] at h
      subst h
      have := C.eq _ _ _ hd
      simpa using this.symm
    | cons x xs => simp at h

end Codec
end P10S2
