import P10.Bound
import P10S2.Types

/-!
# P10S2.Fixture — the S2 fixture profile `fx`

`fx` is an extension of the frozen `P10.S1.profile` (`fx_projection` holds by `rfl`):
S2 adds admission items, a frozen per-item compatibility relation and a total `bundle`,
and changes nothing in S1. `bundle` is order-independent, idempotent, total and faithful
to the per-item relation (prereg §13). These are fixture design choices, not universal
P10 requirements.
-/

namespace P10S2
open P10.S1

/-- Admission-profile: a P10 profile plus items, admissibility, per-item relation, bundle. -/
structure AdmissionProfile extends P10.Profile where
  Item       : Type
  admissible : Item → Bool
  itemCompat : Item → World → Bool
  bundle     : List Item → Evidence
  /-- Decision procedure for `Eπ` (so that `coverageCheck` is executable). -/
  inEb       : Evidence → Bool
  inE_spec   : ∀ e, inE e ↔ inEb e = true
  /-- Fixture identifier the concrete profile artifact must carry (prereg §6a). -/
  fixtureId  : List Nat

inductive FxItem
  | first  (b : Bool)
  | second (b : Bool)
  deriving DecidableEq, Repr

/-- Frozen per-item relation (prereg §13). -/
def fxItemCompat : FxItem → P10.S1.World → Bool
  | .first b,  w => firstBit w == b
  | .second b, w => secondBitOf w == b

/-- The evidence built from the four membership flags (`first false`, `first true`,
`second false`, `second true`). -/
def mkEv (f0 f1 s0 s1 : Bool) : P10.S1.Evidence :=
  if (!f0 && !f1) = true then .outside
  else if ((f0 && f1) || (s0 && s1)) = true then .inconsistent
  else .obs f1 (if s0 = true then some false else if s1 = true then some true else none)

/-- `Bundleπ` for the fixture: total, order-independent, idempotent. -/
def fxBundle (xs : List FxItem) : P10.S1.Evidence :=
  mkEv (xs.contains (.first false)) (xs.contains (.first true))
       (xs.contains (.second false)) (xs.contains (.second true))

def fx : AdmissionProfile :=
  { toProfile := P10.S1.profile
    Item := FxItem
    admissible := fun _ => true
    itemCompat := fxItemCompat
    bundle := fxBundle
    inEb := inEB
    inE_spec := fun _ => Iff.rfl
    fixtureId := bytes% "p10-s2-fx-v0" }

/-- The Lean semantic projection of the fixture is exactly the frozen S1 profile. -/
theorem fx_projection : fx.toProfile = P10.S1.profile := rfl

/-! ### Truth table -/

theorem bundle_truth_nil : fxBundle [] = .outside := by decide
theorem bundle_truth_second (b : Bool) : fxBundle [.second b] = .outside := by
  cases b <;> decide
theorem bundle_truth_eU : fxBundle [.first false] = .obs false none := by decide
theorem bundle_truth_eD :
    fxBundle [.first false, .second false] = .obs false (some false) := by decide
theorem bundle_truth_first_conflict :
    fxBundle [.first false, .first true] = .inconsistent := by decide
theorem bundle_truth_second_conflict :
    fxBundle [.first false, .second false, .second true] = .inconsistent := by decide
theorem bundle_truth_second_conflict_nofirst :
    fxBundle [.second false, .second true] = .outside := by decide

/-! ### Faithfulness core, abstracted over the four membership flags -/

theorem faithful_core (f0 f1 s0 s1 : Bool) (w : P10.S1.World)
    (hE : (!f0 && !f1) = false) :
    compatB (mkEv f0 f1 s0 s1) w = true ↔
      ((f0 = true → firstBit w = false) ∧ (f1 = true → firstBit w = true) ∧
       (s0 = true → secondBitOf w = false) ∧ (s1 = true → secondBitOf w = true)) := by
  cases f0 <;> cases f1 <;> cases s0 <;> cases s1 <;> cases w <;>
    first | (exact absurd hE (by decide)) | decide

theorem mkEv_inE (f0 f1 s0 s1 : Bool) :
    inEB (mkEv f0 f1 s0 s1) = true ↔ (!f0 && !f1) = false := by
  cases f0 <;> cases f1 <;> cases s0 <;> cases s1 <;> decide

/-- Every item of `xs` is compatible with `w` iff each flagged item is. -/
theorem forall_mem_iff (xs : List FxItem) (w : P10.S1.World) :
    (∀ x ∈ xs, fxItemCompat x w = true) ↔
      ((xs.contains (.first false) = true → firstBit w = false) ∧
       (xs.contains (.first true) = true → firstBit w = true) ∧
       (xs.contains (.second false) = true → secondBitOf w = false) ∧
       (xs.contains (.second true) = true → secondBitOf w = true)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hc
      have hm := List.contains_iff_mem.mp hc
      have := h _ hm
      simpa [fxItemCompat] using this
    · intro hc
      have hm := List.contains_iff_mem.mp hc
      have := h _ hm
      simpa [fxItemCompat] using this
    · intro hc
      have hm := List.contains_iff_mem.mp hc
      have := h _ hm
      simpa [fxItemCompat] using this
    · intro hc
      have hm := List.contains_iff_mem.mp hc
      have := h _ hm
      simpa [fxItemCompat] using this
  · rintro ⟨h1, h2, h3, h4⟩ x hx
    have hc : xs.contains x = true := List.contains_iff_mem.mpr hx
    cases x with
    | first b =>
      cases b
      · have := h1 hc; simp [fxItemCompat, this]
      · have := h2 hc; simp [fxItemCompat, this]
    | second b =>
      cases b
      · have := h3 hc; simp [fxItemCompat, this]
      · have := h4 hc; simp [fxItemCompat, this]

/-- **`bundle_faithful`** (exact characterization, prereg §13): inside `Eπ`, the compatible
worlds of `bundle xs` are exactly those compatible with every item. -/
theorem bundle_faithful (xs : List FxItem) :
    fx.toProfile.inE (fxBundle xs) →
    ∀ w, fx.toProfile.inW w →
      (P10.Compatible fx.toProfile (fxBundle xs) w ↔ ∀ x ∈ xs, fx.itemCompat x w = true) := by
  intro hE w _
  have hE' : inEB (fxBundle xs) = true := hE
  have hflag := (mkEv_inE _ _ _ _).mp hE'
  have hc : compatB (fxBundle xs) w = true ↔ _ := faithful_core _ _ _ _ w hflag
  exact hc.trans (forall_mem_iff xs w).symm

/-! ### Order-independence and idempotence -/

theorem fxBundle_of_mem_iff {xs ys : List FxItem} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    fxBundle xs = fxBundle ys := by
  have hc : ∀ x, xs.contains x = ys.contains x := by
    intro x
    have := h x
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact this
  simp only [fxBundle, hc]

theorem bundle_perm {xs ys : List FxItem} (h : xs.Perm ys) : fxBundle xs = fxBundle ys :=
  fxBundle_of_mem_iff (fun _ => h.mem_iff)

theorem mem_eraseDups_aux {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → ∀ x, x ∈ xs.eraseDups ↔ x ∈ xs
  | 0, xs, h, x => by
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp
  | n + 1, [], _, x => by simp
  | n + 1, a :: as, h, x => by
    rw [List.eraseDups_cons]
    have hlen : (as.filter fun b => !b == a).length ≤ n :=
      Nat.le_trans (List.length_filter_le _ _) (by simpa using h)
    have ih := mem_eraseDups_aux n _ hlen x
    simp only [List.mem_cons, ih, List.mem_filter]
    constructor
    · rintro (h1 | ⟨h1, _⟩)
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (h1 | h1)
      · exact Or.inl h1
      · by_cases hx : x = a
        · exact Or.inl hx
        · exact Or.inr ⟨h1, by simp [hx]⟩

theorem bundle_dedup (xs : List FxItem) : fxBundle xs.eraseDups = fxBundle xs :=
  fxBundle_of_mem_iff (fun x => mem_eraseDups_aux xs.length xs (Nat.le_refl _) x)

/-- **`bundle_refines`** (monotonicity; a corollary of `bundle_faithful`). -/
theorem bundle_refines {xs ys : List FxItem} (hsub : xs ⊆ ys)
    (hx : fx.toProfile.inE (fxBundle xs)) (hy : fx.toProfile.inE (fxBundle ys)) :
    ∀ w, fx.toProfile.inW w →
      P10.Compatible fx.toProfile (fxBundle ys) w → P10.Compatible fx.toProfile (fxBundle xs) w := by
  intro w hw hcy
  have h1 := (bundle_faithful ys hy w hw).mp hcy
  exact (bundle_faithful xs hx w hw).mpr (fun x hxm => h1 x (hsub hxm))

end P10S2
