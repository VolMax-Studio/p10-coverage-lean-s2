import P10S2.Coverage

/-!
# P10S2.CoverageSpec — what `accept` implies (prereg §8), and the soundness theorems

`CoreSpec` is the declarative content of C3–C13 over a subject view `W`. There are one profile
commitment `p`, one instance commitment `ci` and one closure `k` (each unique among the valid owner
entries of its kind), and:

* `p` carries exactly the committed profile digest and, like `ci`, precedes every
  `RelevantAdmission`; `ci`'s payload equals the frozen commitment;
* no valid owner adjudication cites a non-owner lifecycle entry (C5);
* the closure's refs are strictly ascending, duplicate-free and equal, as lists, to the
  `RelevantAdmission`s before `k`; none lies in `(k, size)`;
* at least one valid owner adjudication follows `k`, and **every** one cites exactly `(p, ci, k)` (C11);
* `e = Bundle(refs) ∈ Eπ` (C12) and the closure's `closed_evidence_set_digest` is
  `EvidenceDigestV0(e)` (C13).

`CoverageSpecV` states the same over an abstract log view `V` (its subject view), under the
premise `TranscriptFaithful T V`, which Lean cannot discharge (TB2).

Premises and boundaries that this file does NOT discharge (prereg TB2–TB6): `TranscriptFaithful`,
the key map and admitter set frozen by the committed profile (TB4), checkpoint selection and
freshness (TB6): nothing is claimed about leaves at `idx ≥ size(S_R)`. Recomputing
`LogIdentityV0` and executing `LeafEncodeV0` are S2b obligations (§16).
-/

namespace P10S2
open P10.Sha256 (sha256)

variable {Item : Type}

/-- `f` is a RelevantAdmission of the view. -/
def Rel (c : Ctx Item) (W : LogView Item) (f : Nat) : Prop :=
  f < W.size ∧ relevantAt c W f = true

structure CoreSpec (π : AdmissionProfile) (c : Ctx π.Item) (W : LogView π.Item)
    (e : π.Evidence) : Prop where
  sel : ∃ p ci k cl,
    (p < W.size ∧ profileAt c W p = some c.inst.profileDigest ∧
      (∀ j d, j < W.size → profileAt c W j = some d → j = p) ∧
      ∀ f, Rel c W f → p < f) ∧
    (ci < W.size ∧ commitAt c W ci = some c.inst ∧
      (∀ j ic, j < W.size → commitAt c W j = some ic → j = ci) ∧
      ∀ f, Rel c W f → ci < f) ∧
    (k < W.size ∧ closureAt c W k = some cl ∧
      (∀ j cl', j < W.size → closureAt c W j = some cl' → j = k) ∧
      List.Pairwise (· < ·) cl.orderedAdmissionRefs ∧
      cl.orderedAdmissionRefs.Nodup ∧
      cl.orderedAdmissionRefs = (List.range k).filter (relevantAt c W) ∧
      (∀ i, k < i → i < W.size → relevantAt c W i = false) ∧
      (∃ j, k < j ∧ j < W.size ∧ ∃ r, adjAt c W j = some r) ∧
      (∀ j a b d, k < j → j < W.size → adjAt c W j = some (a, b, d) →
        a = p ∧ b = ci ∧ d = k) ∧
      e = π.bundle (cl.orderedAdmissionRefs.filterMap (itemAt W)) ∧ π.inE e ∧
      cl.closedEvidenceSetDigest = evidenceDigestV0 (π.evidenceTok e))
  noCitedNonOwner : ∀ j a b d, j < W.size → adjAt c W j = some (a, b, d) →
    nonOwnerLifecycleAt c W a = false ∧ nonOwnerLifecycleAt c W b = false ∧
      nonOwnerLifecycleAt c W d = false

/-! ### Small list/Bool facts -/

theorem mem_idx_pairs {β : Type} (n : Nat) (f : Nat → Option β) (j : Nat) (x : β) :
    (j, x) ∈ (List.range n).filterMap (fun i => (f i).map fun y => (i, y)) ↔
      j < n ∧ f j = some x := by
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, y, hy, rfl, rfl⟩
    exact ⟨hi, hy⟩
  · rintro ⟨hj, hx⟩
    exact ⟨j, hj, x, hx, rfl, rfl⟩

theorem strictAscNat_pairwise : ∀ (l : List Nat), strictAscNat l = true → List.Pairwise (· < ·) l
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: rest, h => by
    simp only [strictAscNat, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hxy, hrest⟩ := h
    have ih := strictAscNat_pairwise (y :: rest) hrest
    refine List.Pairwise.cons ?_ ih
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hxy
    · have := (List.pairwise_cons.mp ih).1 z hz'
      omega

theorem beforeAll_spec {c : Ctx Item} {W : LogView Item} {i : Nat}
    (h : beforeAll c W i = true) : ∀ f, Rel c W f → i < f := by
  intro f hf
  unfold beforeAll at h
  have hm : f ∈ (List.range W.size).filter (relevantAt c W) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hf.1, hf.2⟩
  exact of_decide_eq_true (List.all_eq_true.mp h f hm)

theorem finish_stage {E : Type} {b : Bool} {o k : CoverageOutcome E} {e : E}
    (ho : ∀ e', o ≠ .accept e') (h : finish (stage b o) k = .accept e) :
    b = true ∧ k = .accept e := by
  cases b
  · simp only [stage, finish] at h
    exact absurd h (ho e)
  · simpa [stage, finish] using h

/-! ### Soundness of the core (C3–C13) -/

theorem coreCheck_sound (π : AdmissionProfile) (c : Ctx π.Item) (W : LogView π.Item)
    (e : π.Evidence) (h : coreCheck π c W = .accept e) : CoreSpec π c W e := by
  unfold coreCheck at h
  simp only [] at h
  split at h
  · simp at h
  · simp at h
  · rename_i p d hprofs
    obtain ⟨h3a, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨h3b, h⟩ := finish_stage (by intro e'; simp) h
    split at h
    · simp at h
    · simp at h
    · rename_i ci ic hcommits
      obtain ⟨h4a, h⟩ := finish_stage (by intro e'; simp) h
      obtain ⟨h4b, h⟩ := finish_stage (by intro e'; simp) h
      obtain ⟨h5, h⟩ := finish_stage (by intro e'; simp) h
      split at h
      · simp at h
      · simp at h
      · rename_i k cl hclosures
        obtain ⟨h7, h⟩ := finish_stage (by intro e'; simp) h
        obtain ⟨h8, h⟩ := finish_stage (by intro e'; simp) h
        obtain ⟨h9, h⟩ := finish_stage (by intro e'; simp) h
        obtain ⟨h10, h⟩ := finish_stage (by intro e'; simp) h
        split at h
        · simp at h
        · rename_i x xs hafter
          obtain ⟨h11, h⟩ := finish_stage (by intro e'; simp) h
          have hp : (p, d) ∈ List.filterMap
              (fun i => Option.map (fun d => (i, d)) (profileAt c W i)) (List.range W.size) := by
            rw [hprofs]; simp
          rw [mem_idx_pairs] at hp
          have hd : d = c.inst.profileDigest := of_decide_eq_true h3a
          have hci : (ci, ic) ∈ List.filterMap
              (fun i => Option.map (fun ic => (i, ic)) (commitAt c W i)) (List.range W.size) := by
            rw [hcommits]; simp
          rw [mem_idx_pairs] at hci
          have hic : ic = c.inst := of_decide_eq_true h4a
          have hk : (k, cl) ∈ List.filterMap
              (fun i => Option.map (fun cl => (i, cl)) (closureAt c W i)) (List.range W.size) := by
            rw [hclosures]; simp
          rw [mem_idx_pairs] at hk
          have hR : cl.orderedAdmissionRefs = (List.range k).filter (relevantAt c W) :=
            of_decide_eq_true h9
          split at h
          · rename_i hE
            obtain ⟨h13, h⟩ := finish_stage (by intro e'; simp) h
            simp only [CoverageOutcome.accept.injEq] at h
            subst h
            refine ⟨⟨p, ci, k, cl, ⟨hp.1, ?_, ?_, beforeAll_spec h3b⟩, ⟨hci.1, ?_, ?_, beforeAll_spec h4b⟩,
              ⟨hk.1, hk.2, ?_, strictAscNat_pairwise _ h7, ?_, hR, ?_, ?_, ?_, rfl,
                (π.inE_spec _).mpr hE, of_decide_eq_true h13⟩⟩, ?_⟩
            · rw [hp.2, hd]
            · intro j d' hj hd'
              have hm : (j, d') ∈ List.filterMap
                  (fun i => Option.map (fun d => (i, d)) (profileAt c W i)) (List.range W.size) :=
                (mem_idx_pairs _ _ _ _).mpr ⟨hj, hd'⟩
              rw [hprofs] at hm
              simp at hm
              exact hm.1
            · rw [hci.2, hic]
            · intro j ic' hj hc'
              have hm : (j, ic') ∈ List.filterMap
                  (fun i => Option.map (fun ic => (i, ic)) (commitAt c W i)) (List.range W.size) :=
                (mem_idx_pairs _ _ _ _).mpr ⟨hj, hc'⟩
              rw [hcommits] at hm
              simp at hm
              exact hm.1
            · intro j cl' hj hc'
              have hm : (j, cl') ∈ List.filterMap
                  (fun i => Option.map (fun cl => (i, cl)) (closureAt c W i)) (List.range W.size) :=
                (mem_idx_pairs _ _ _ _).mpr ⟨hj, hc'⟩
              rw [hclosures] at hm
              simp at hm
              exact hm.1
            · exact (strictAscNat_pairwise _ h7).imp (fun h => Nat.ne_of_lt h)
            · intro i hki hi
              cases hr : relevantAt c W i
              · rfl
              · exfalso
                have hany : (List.range W.size).any
                    (fun i => decide (k < i) && relevantAt c W i) = true :=
                  List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simp [hki, hr]⟩
                rw [hany] at h10
                exact absurd h10 (by decide)
            · have hxm : x ∈ List.filter (fun ar => decide (k < ar.1)) (List.filterMap
                  (fun i => Option.map (fun r => (i, r)) (adjAt c W i)) (List.range W.size)) := by
                rw [hafter]; simp
              obtain ⟨hxa, hxk⟩ := List.mem_filter.mp hxm
              obtain ⟨j, r⟩ := x
              have hm' := (mem_idx_pairs _ _ _ _).mp hxa
              exact ⟨j, of_decide_eq_true hxk, hm'.1, r, hm'.2⟩
            · intro j a b d' hkj hj hadj
              have hm : (j, (a, b, d')) ∈ List.filterMap
                  (fun i => Option.map (fun r => (i, r)) (adjAt c W i)) (List.range W.size) :=
                (mem_idx_pairs _ _ _ _).mpr ⟨hj, hadj⟩
              have hma : (j, (a, b, d')) ∈ List.filter (fun ar => decide (k < ar.1))
                  (List.filterMap (fun i => Option.map (fun r => (i, r)) (adjAt c W i))
                    (List.range W.size)) :=
                List.mem_filter.mpr ⟨hm, by simpa using hkj⟩
              have := List.all_eq_true.mp h11 _ hma
              simp only [Bool.and_eq_true, decide_eq_true_eq] at this
              exact ⟨this.1.1, this.1.2, this.2⟩
            · intro j a b d' hj hadj
              have hm : (j, (a, b, d')) ∈ List.filterMap
                  (fun i => Option.map (fun r => (i, r)) (adjAt c W i)) (List.range W.size) :=
                (mem_idx_pairs _ _ _ _).mpr ⟨hj, hadj⟩
              have := List.all_eq_true.mp h5 _ hm
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
              exact ⟨this.1.1, this.1.2, this.2⟩
          · simp at h

/-! ### The transcript-level specification (C1, C1a–C1c, C2 and the core) -/

/-- What C1 (profile-artifact fields), C1a, C1b (admitters) and C1c establish about a decoded
profile artifact `prof` relative to the frozen commitment `inst` (prereg v0.2.5 §7). -/
structure C1FactsV (π : AdmissionProfile) (inst : InstanceCommitment)
    (prof : ProfileArtifact) : Prop where
  fixture : prof.fixtureId.1 = π.fixtureId
  normative : prof.normativeProfileDigest.1 = s1Spec
  s1Token : prof.s1ProfileToken.1 = s1ProfileTok
  ownerIsIssuer : inst.instanceOwnerIss = inst.issuerId
  issuerToken : allTokB inst.issuerId.bytes = true
  subjectDerived : inst.instanceSubject = subjectDeriveV0 inst.issuerId inst.requestId
  ownerNotAdmitter : (admitterIss prof).contains inst.instanceOwnerIss = false
  admittersDigest : inst.authorizedAdmitterSetDigest = authorizedAdmittersDigestOf prof
  subjectDerivationDigest : inst.subjectDerivationDigest = subjectDerivationDigestV0 prof
  leafEncodingProfileDigest : inst.leafEncodingProfileDigest = leafEncodingProfileDigestV0 prof
  evidenceScopeDigest : inst.evidenceScopeDigest = evidenceScopeDigestV0 prof
  admissionRuleDigest : inst.admissionRuleDigest = admissionRuleDigestV0 prof
  coverageRuleDigest : inst.coverageRuleDigest = coverageRuleDigestV0 prof

/-- Everything `accept` implies about a transcript `T`, relative to `inst` and `pB`. -/
structure CoverageSpecT (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Transcript π.Item) (e : π.Evidence) : Prop where
  rowsContiguous : T.rows.map Row.idx = List.range T.checkpoint.size
  detailedMatch : T.detailed.map DetailedEntry.idx = matchIdxs inst.instanceSubject T.rows
  logIdentity : T.logIdentityDigest = inst.logIdentityDigest
  profileDigest : sha256 pB = inst.profileDigest.bytes
  noUnavailableRow : ∀ r ∈ T.rows, rowUnavailable r = false
  payloadsAvailable : ∀ d ∈ T.detailed, d.payload.isSome = true
  profile : ∃ prof, decodeProfileArtifact pB = some prof ∧ C1FactsV π inst prof ∧
    T.keyResolutionDigest = keyResolutionDigestV0 prof.keyResolution ∧
    (∀ d ∈ T.detailed,
      authorizedIss ⟨π.admissible, inst, admitterIss prof⟩ d.iss = true →
        d.sig ≠ .keyUnavailable) ∧
    CoreSpec π ⟨π.admissible, inst, admitterIss prof⟩ (viewT inst.instanceSubject T) e

/-- **`coverage_sound`**: an accepted transcript satisfies the coverage specification. -/
theorem coverage_sound (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Transcript π.Item) (e : π.Evidence)
    (h : coverageCheck π inst pB T = .accept e) : CoverageSpecT π inst pB T e := by
  unfold coverageCheck at h
  simp only [] at h
  obtain ⟨h1a, h⟩ := finish_stage (by intro e'; simp) h
  obtain ⟨h1b, h⟩ := finish_stage (by intro e'; simp) h
  obtain ⟨h1c, h⟩ := finish_stage (by intro e'; simp) h
  obtain ⟨h1d, h⟩ := finish_stage (by intro e'; simp) h
  split at h
  · simp at h
  · rename_i prof hprof
    obtain ⟨h1e, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨ha1, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨ha2, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨ha3, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hb0, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hb1, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hb2, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hc1, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hc2, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hc3, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hc4, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨hc5, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨h2a, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨h2b, h⟩ := finish_stage (by intro e'; simp) h
    obtain ⟨h2c, h⟩ := finish_stage (by intro e'; simp) h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1e
    have hcore := coreCheck_sound _ _ _ _ h
    refine ⟨of_decide_eq_true h1a, of_decide_eq_true h1b, of_decide_eq_true h1c,
      of_decide_eq_true h1d, ?_, ?_, prof, hprof,
      ⟨h1e.1.1, h1e.1.2, h1e.2, of_decide_eq_true ha1, ha2, of_decide_eq_true ha3,
        by simpa using hb0, of_decide_eq_true hb1, of_decide_eq_true hc1,
        of_decide_eq_true hc2, of_decide_eq_true hc3, of_decide_eq_true hc4,
        of_decide_eq_true hc5⟩,
      of_decide_eq_true hb2, ?_, hcore⟩
    · intro r hr
      cases hrr : rowUnavailable r
      · rfl
      · exfalso
        have hany : T.rows.any rowUnavailable = true := List.any_eq_true.mpr ⟨r, hr, hrr⟩
        rw [hany] at h2a
        exact absurd h2a (by decide)
    · intro d hd
      exact List.all_eq_true.mp h2b d hd
    · intro d hd hauth
      have := List.all_eq_true.mp h2c d hd
      cases hs : d.sig
      · simp
      · simp
      · rw [hs] at this
        simp [hauth] at this

/-! ### Transport to an abstract log view (TB2) -/

/-- How a row of `T` must agree with the real log view. -/
def rowFaith (V : LogView Item) (r : Row) : Prop :=
  match r.status with
  | .available s => ∃ lf, V.leaf r.idx = some lf ∧ lf.sub = s
  | .unavailable => V.leaf r.idx = none

/-- How a detailed entry of `T` must agree with the real log view. -/
def detFaith (V : LogView Item) (d : DetailedEntry Item) : Prop :=
  ∃ lf, V.leaf d.idx = some lf ∧ lf.iss = d.iss ∧ lf.kind = d.kind ∧ lf.sig = d.sig ∧
    lf.payload = d.payload

/-- `TranscriptFaithful(T, V)` (prereg TB2): sizes agree and every row and detailed entry of `T`
agrees with `V.leaf` at its index, availability included. Lean cannot discharge it: it is S2b's
obligation (together with root reconstruction, checkpoint signature and correct observation). -/
def TranscriptFaithful (T : Transcript Item) (V : LogView Item) : Prop :=
  T.checkpoint.size = V.size ∧ (∀ r ∈ T.rows, rowFaith V r) ∧
    (∀ d ∈ T.detailed, detFaith V d)

/-- The subject view `SubjectView(L, S_R, instance_subject)` of a log view (profile §2.6). -/
def LogView.subj (V : LogView Item) (sub : Subject) : LogView Item where
  size := V.size
  leaf i :=
    if i < V.size then
      (match V.leaf i with
       | some lf => if lf.sub = sub then some lf else none
       | none => none)
    else none

theorem matchIdxs_mem (sub : Subject) (rows : List Row) (i : Nat) :
    i ∈ matchIdxs sub rows ↔ ∃ r ∈ rows, r.idx = i ∧ r.status = .available sub := by
  unfold matchIdxs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨r, hr, ?_⟩
    obtain ⟨idx, st⟩ := r
    cases st with
    | unavailable => simp at hm
    | available s =>
      by_cases hs : s = sub
      · simp [hs] at hm
        simp [hm, hs]
      · simp [hs] at hm
  · rintro ⟨r, hr, hi, hst⟩
    refine ⟨r, hr, ?_⟩
    obtain ⟨idx, st⟩ := r
    simp only at hi hst
    subst hst
    simp [hi]

theorem inj_on_of_nodup_map' {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => nomatch hx
  | a :: l, hnd, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hna, hnd'⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (hxy ▸ List.mem_map.mpr ⟨y, hy', rfl⟩) hna
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (hxy ▸ List.mem_map.mpr ⟨x, hx', rfl⟩) hna
      · exact inj_on_of_nodup_map' f l hnd' x hx' y hy' hxy

theorem viewT_eq_subj (sub : Subject) (T : Transcript Item) (V : LogView Item)
    (hrows : T.rows.map Row.idx = List.range T.checkpoint.size)
    (hdet : T.detailed.map DetailedEntry.idx = matchIdxs sub T.rows)
    (hf : TranscriptFaithful T V) : viewT sub T = V.subj sub := by
  obtain ⟨hsize, hrf, hdf⟩ := hf
  have hnd : (T.rows.map Row.idx).Nodup := by rw [hrows]; exact List.nodup_range
  have hinj : ∀ r ∈ T.rows, ∀ r' ∈ T.rows, r.idx = r'.idx → r = r' :=
    fun r hr r' hr' h => inj_on_of_nodup_map' Row.idx T.rows hnd r hr r' hr' h
  -- a detailed entry at `i` forces an available, matching row at `i`
  have hdet_row : ∀ d ∈ T.detailed, ∃ r ∈ T.rows, r.idx = d.idx ∧ r.status = .available sub := by
    intro d hd
    have hm : d.idx ∈ matchIdxs sub T.rows := by
      rw [← hdet]; exact List.mem_map.mpr ⟨d, hd, rfl⟩
    exact (matchIdxs_mem sub T.rows d.idx).mp hm
  have hrow_det : ∀ r ∈ T.rows, r.status = .available sub → ∃ d ∈ T.detailed, d.idx = r.idx := by
    intro r hr hst
    have hm : r.idx ∈ matchIdxs sub T.rows := (matchIdxs_mem sub T.rows r.idx).mpr ⟨r, hr, rfl, hst⟩
    rw [← hdet] at hm
    obtain ⟨d, hd, hdi⟩ := List.mem_map.mp hm
    exact ⟨d, hd, hdi⟩
  have hnone_of : ∀ i, (∀ d ∈ T.detailed, d.idx = i → False) →
      (T.detailed.find? fun d => decide (d.idx = i)) = none := by
    intro i hno
    rw [List.find?_eq_none]
    intro d hd hb
    exact hno d hd (of_decide_eq_true hb)
  have hmain : ∀ i, (viewT sub T).leaf i = (V.subj sub).leaf i := by
    intro i
    unfold viewT LogView.subj
    simp only []
    by_cases hi : i < T.checkpoint.size
    · have hiV : i < V.size := hsize ▸ hi
      simp only [hi, hiV, if_true]
      have hir : i ∈ T.rows.map Row.idx := by rw [hrows]; exact List.mem_range.mpr hi
      obtain ⟨r, hr, hri⟩ := List.mem_map.mp hir
      have hrfr := hrf r hr
      obtain ⟨ridx, rst⟩ := r
      simp only at hri
      subst hri
      cases rst with
      | unavailable =>
        simp only [rowFaith] at hrfr
        rw [hrfr]
        simp only []
        rw [hnone_of]
        · simp
        · intro d hd hdi
          obtain ⟨r', hr', hri', hst'⟩ := hdet_row d hd
          have hre : r' = ⟨ridx, .unavailable⟩ := hinj _ hr' _ hr (by simp [hri', hdi])
          subst hre
          simp at hst'
      | available s =>
        simp only [rowFaith] at hrfr
        obtain ⟨lf, hlf, hlfs⟩ := hrfr
        rw [hlf]
        simp only []
        by_cases hs : s = sub
        · subst hs
          have hlfs' : lf.sub = s := hlfs
          obtain ⟨d, hd, hdi⟩ := hrow_det ⟨ridx, .available s⟩ hr rfl
          have hfind : (T.detailed.find? fun d => decide (d.idx = ridx)).isSome = true := by
            rw [List.find?_isSome]
            exact ⟨d, hd, by simpa using hdi⟩
          cases hfd : T.detailed.find? (fun d => decide (d.idx = ridx)) with
          | none => rw [hfd] at hfind; simp at hfind
          | some d' =>
            have hd'mem := List.mem_of_find?_eq_some hfd
            have hd'b := List.find?_some hfd
            have hd'idx : d'.idx = ridx := of_decide_eq_true hd'b
            obtain ⟨lf', hlf', h1, h2, h3, h4⟩ := hdf d' hd'mem
            rw [hd'idx, hlf] at hlf'
            have hlfeq : lf = lf' := Option.some.inj hlf'
            subst hlfeq
            simp only [Option.map_some, toFacts]
            rw [if_pos hlfs']
            congr 1
            obtain ⟨lsub, liss, lkind, lsig, lpay⟩ := lf
            simp only at hlfs' h1 h2 h3 h4
            subst hlfs'; subst h1; subst h2; subst h3; subst h4
            rfl
        · have hlfne : ¬ lf.sub = sub := by rw [hlfs]; exact hs
          rw [if_neg hlfne]
          rw [hnone_of]
          · simp
          · intro d hd hdi
            obtain ⟨r', hr', hri', hst'⟩ := hdet_row d hd
            have hre : r' = ⟨ridx, .available s⟩ := hinj _ hr' _ hr (by simp [hri', hdi])
            subst hre
            have hst'' : RowStatus.available s = RowStatus.available sub := hst'
            injection hst'' with hss
            exact hs hss
    · have hiV : ¬ i < V.size := fun h => hi (hsize ▸ h)
      simp [hi, hiV]
  have hsz : (viewT sub T).size = (V.subj sub).size := by
    simp [viewT, LogView.subj, hsize]
  cases hv : viewT sub T with
  | mk s1 l1 =>
  cases hw : V.subj sub with
  | mk s2 l2 =>
    have e1 : s1 = s2 := by
      have := hsz; rw [hv, hw] at this; exact this
    have e2 : l1 = l2 := by
      funext i
      have := hmain i; rw [hv, hw] at this; exact this
    rw [e1, e2]

/-! ### The view-level specification (prereg §8, `CoverageSpecV`) -/

/-- Everything `accept` implies about the abstract log view `V` through `S_R`, given a faithful
transcript. In particular, over `SubjectView(V)`: one valid owner profile commitment with the
committed digest and one commitment precede every `RelevantAdmission`; exactly one valid owner
closure `k`; its refs are exactly, as ascending duplicate-free lists, the `RelevantAdmission`s
before `k`; no `RelevantAdmission` lies in `(k, size)`; every owner adjudication after `k` cites
the selected profile, commitment and closure; `e = Bundle(refs) ∈ Eπ` and the closure's
`closed_evidence_set_digest` is `EvidenceDigestV0(e)`. All leaves below `size` were available. -/
structure CoverageSpecV (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (V : LogView π.Item) (e : π.Evidence) : Prop where
  profileDigest : sha256 pB = inst.profileDigest.bytes
  allAvailable : ∀ i, i < V.size → (V.leaf i).isSome = true
  profile : ∃ prof, decodeProfileArtifact pB = some prof ∧ C1FactsV π inst prof ∧
    CoreSpec π ⟨π.admissible, inst, admitterIss prof⟩ (V.subj inst.instanceSubject) e

/-- **`coverage_sound_view`**: under `TranscriptFaithful T V` (TB2), an accepted transcript yields
the coverage specification over the log view itself, not only over `T`. -/
theorem coverage_sound_view (π : AdmissionProfile) (inst : InstanceCommitment) (pB : Bytes)
    (T : Transcript π.Item) (V : LogView π.Item) (e : π.Evidence)
    (hf : TranscriptFaithful T V)
    (h : coverageCheck π inst pB T = .accept e) : CoverageSpecV π inst pB V e := by
  have hs := coverage_sound π inst pB T e h
  have hv := viewT_eq_subj inst.instanceSubject T V hs.rowsContiguous hs.detailedMatch hf
  refine ⟨hs.profileDigest, ?_, ?_⟩
  · intro i hi
    have hiT : i < T.checkpoint.size := hf.1 ▸ hi
    have hir : i ∈ T.rows.map Row.idx := by
      rw [hs.rowsContiguous]; exact List.mem_range.mpr hiT
    obtain ⟨r, hr, hri⟩ := List.mem_map.mp hir
    have hrf := hf.2.1 r hr
    have hru := hs.noUnavailableRow r hr
    obtain ⟨ridx, rst⟩ := r
    cases rst with
    | unavailable => simp [rowUnavailable] at hru
    | available sb =>
      simp only [rowFaith] at hrf
      obtain ⟨lf, hlf, _⟩ := hrf
      simp only at hri
      subst hri
      rw [hlf]
      rfl
  · obtain ⟨prof, hp, hc1, _, _, hcore⟩ := hs.profile
    refine ⟨prof, hp, hc1, ?_⟩
    rw [hv] at hcore
    exact hcore

end P10S2
