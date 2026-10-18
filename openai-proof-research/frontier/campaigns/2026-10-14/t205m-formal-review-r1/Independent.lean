import T205M
import Controls

/- Independent reviewer checks for the frozen T205M scoped support. MIT.
Reviewer-written; imports the author modules only to pin their exact types. -/
namespace T205MReview

open T205M

section Pin

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-! Statement pinning: each `example` restates an author declaration in the reviewer's
own words; it typechecks only if the author's type has exactly this meaning. -/

example (s : Finset α) : IsIdeal s ↔ ∀ x y : α, y ∈ s → x ≤ y → x ∈ s :=
  ⟨fun h _ _ hy hxy => h hy hxy, fun h _ _ hy hxy => h _ _ hy hxy⟩

omit [DecidableEq α] in
/-- `IsIdeal` is Mathlib's `IsLowerSet` on the coerced set: genuine downward closure. -/
theorem isIdeal_iff_isLowerSet (s : Finset α) : IsIdeal s ↔ IsLowerSet (s : Set α) := by
  constructor
  · intro h a b hba ha
    exact Finset.mem_coe.mpr (h (Finset.mem_coe.mp ha) hba)
  · intro h x y hy hxy
    exact Finset.mem_coe.mp (h hxy (Finset.mem_coe.mpr hy))

example {s t : Finset α} (hs : IsIdeal s) (ht : IsIdeal t) (hst : s ⊆ t) (r : ℕ)
    (hsr : s.card ≤ r) (hrt : r ≤ t.card) :
    ∃ u : Finset α, IsIdeal u ∧ s ⊆ u ∧ u ⊆ t ∧ u.card = r :=
  ideal_interval_rank hs ht hst hsr hrt

example [Fintype α] (s : Finset α) (hs : IsIdeal s)
    (hu : ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s) :
    ∀ a ∈ s, ∀ b ∉ s, a ≤ b :=
  fun _ ha _ hb => unique_rank_cross_comparable hs hu ha hb

example [Fintype α] (s : Finset α) (hs : IsIdeal s) (a b : α)
    (ha : a ∈ s) (hb : b ∉ s) (hab : ¬a ≤ b) :
    ∃ t : Finset α, IsIdeal t ∧ t.card = s.card ∧ t ≠ s :=
  exists_second_ideal_of_incomparable hs ha hb hab

example [Fintype α] (r : ℕ) (hr : r ≤ Fintype.card α)
    (hno : ∀ s : Finset α, IsIdeal s → s.card = r → ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b) :
    ∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧ s.card = r ∧ t.card = r ∧ s ≠ t :=
  two_ideals_of_no_cut hr hno

/-! The `_hs` hypothesis of `unique_rank_cross_comparable` is implied by uniqueness. -/

theorem ideal_of_unique [Fintype α] {s : Finset α}
    (hu : ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s) : IsIdeal s := by
  have huniv : IsIdeal (Finset.univ : Finset α) := by
    intro x _ _ _
    exact Finset.mem_univ x
  obtain ⟨u, hi, -, -, hc⟩ := ideal_interval_rank empty_ideal huniv
    (Finset.empty_subset _) (r := s.card) (by simp) (Finset.card_le_univ s)
  exact hu u hi hc ▸ hi

theorem cross_comparable_without_hs [Fintype α] {s : Finset α}
    (hu : ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s)
    {a b : α} (ha : a ∈ s) (hb : b ∉ s) : a ≤ b :=
  unique_rank_cross_comparable (ideal_of_unique hu) hu ha hb

/-! Converse: an ordered cut is the unique ideal of its size. Together with the author
theorem this is an equivalence, so the hypotheses are exact rather than over-strong. -/

theorem unique_of_cut {s : Finset α} (hcut : ∀ a ∈ s, ∀ b ∉ s, a ≤ b) :
    ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s := by
  intro t ht hc
  by_contra hne
  have hts : ¬t ⊆ s := fun hsub =>
    hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  obtain ⟨b, hbt, hbs⟩ := Finset.not_subset.mp hts
  have hst : ¬s ⊆ t := fun hsub =>
    hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hst
  exact hat (ht hbt (hcut a has b hbs))

theorem no_cut_of_two_ideals {r : ℕ}
    (h2 : ∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧ s.card = r ∧ t.card = r ∧ s ≠ t) :
    ∀ s : Finset α, IsIdeal s → s.card = r → ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b := by
  obtain ⟨s₁, s₂, h₁, h₂, c₁, c₂, hne⟩ := h2
  intro s _ hc
  by_contra hno
  push Not at hno
  have hu := unique_of_cut hno
  exact hne ((hu s₁ h₁ (by omega)).trans (hu s₂ h₂ (by omega)).symm)

/-- Exact characterization of the author's two-ideal criterion at a feasible rank. -/
theorem two_ideals_iff_no_cut [Fintype α] {r : ℕ} (hr : r ≤ Fintype.card α) :
    (∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧ s.card = r ∧ t.card = r ∧ s ≠ t) ↔
      ∀ s : Finset α, IsIdeal s → s.card = r → ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b :=
  ⟨no_cut_of_two_ideals, two_ideals_of_no_cut hr⟩

end Pin

/-! Translation to the parent's cell posets: any finite set of cells in ℕ × ℕ, with the
induced componentwise order, is a valid instance. -/

example (x y : ℕ × ℕ) : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := Prod.le_def

example (S : Finset (ℕ × ℕ)) (x y : S) : x ≤ y ↔ (x : ℕ × ℕ) ≤ (y : ℕ × ℕ) := Iff.rfl

theorem cells_ideal_every_size (S : Finset (ℕ × ℕ)) {r : ℕ} (hr : r ≤ S.card) :
    ∃ u : Finset S, IsIdeal u ∧ u.card = r := by
  have hu : IsIdeal (Finset.univ : Finset S) := by
    intro x _ _ _
    exact Finset.mem_univ x
  obtain ⟨u, hi, -, -, hc⟩ := ideal_interval_rank empty_ideal hu
    (Finset.empty_subset _) (r := r) (by simp) (by simpa using hr)
  exact ⟨u, hi, hc⟩

theorem cells_two_ideals_of_no_cut (S : Finset (ℕ × ℕ)) {r : ℕ} (hr : r ≤ S.card)
    (hno : ∀ A : Finset S, IsIdeal A → A.card = r → ∃ a ∈ A, ∃ b ∉ A, ¬a ≤ b) :
    ∃ A B : Finset S, IsIdeal A ∧ IsIdeal B ∧ A.card = r ∧ B.card = r ∧ A ≠ B :=
  two_ideals_of_no_cut (by simpa using hr) hno

/-! Nonvacuity and necessity controls written by the reviewer. -/

open T205MControls

theorem not_every_set_is_ideal : ¬IsIdeal ({1} : Finset (Fin 2)) := by
  intro h
  have h0 := h (x := 0) (y := 1) (by simp) (by decide)
  simp at h0

theorem card_two : Fintype.card Two = 2 := rfl

theorem antichain_no_cut :
    ∀ s : Finset Two, IsIdeal s → s.card = 1 → ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b := by
  simp only [IsIdeal]
  decide

theorem antichain_two_ideals : ∃ s t : Finset Two,
    IsIdeal s ∧ IsIdeal t ∧ s.card = 1 ∧ t.card = 1 ∧ s ≠ t :=
  two_ideals_of_no_cut (by rw [card_two]; omega) antichain_no_cut

theorem no_cut_hypothesis_needed : ¬∃ s t : Finset (Fin 4),
    IsIdeal s ∧ IsIdeal t ∧ s.card = 2 ∧ t.card = 2 ∧ s ≠ t := by
  rintro ⟨s, t, hs, ht, hsc, htc, hne⟩
  have hc : chainPrefix.card = 2 := rfl
  exact hne ((chainPrefix_unique s hs (hsc.trans hc.symm)).trans
    (chainPrefix_unique t ht (htc.trans hc.symm)).symm)

theorem two_ideal_rank_bound_needed : ¬∀ r : ℕ,
    (∀ s : Finset Two, IsIdeal s → s.card = r → ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b) →
      ∃ s t : Finset Two, IsIdeal s ∧ IsIdeal t ∧ s.card = r ∧ t.card = r ∧ s ≠ t := by
  intro h
  have hbig : ∀ s : Finset Two, s.card ≠ 3 := by
    intro s hs
    have := Finset.card_le_univ s
    rw [card_two] at this
    omega
  obtain ⟨s, -, -, -, hs, -, -⟩ := h 3 (fun s _ hs => absurd hs (hbig s))
  exact hbig s hs

theorem interval_lower_bound_needed : ¬∃ u : Finset (Fin 2),
    IsIdeal u ∧ (Finset.univ : Finset (Fin 2)) ⊆ u ∧ u ⊆ Finset.univ ∧ u.card = 0 := by
  rintro ⟨u, -, hsu, -, hc⟩
  have := Finset.card_le_card hsu
  simp at this
  omega

theorem interval_upper_ideal_needed : ¬∃ u : Finset (Fin 2),
    IsIdeal u ∧ (∅ : Finset (Fin 2)) ⊆ u ∧ u ⊆ {1} ∧ u.card = 1 := by
  simp only [IsIdeal]
  decide

end T205MReview

/-! Complete declaration inventory of the two author modules, with kernel axiom closure. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for modName in [`T205M, `Controls] do
    let some idx := env.getModuleIdx? modName | throwError m!"module {modName} missing"
    let mut names : Array Name := #[]
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then
        names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    IO.println s!"MODULE {modName} constants={names.size}"
    for n in names do
      let some ci := env.find? n | throwError m!"lost {n}"
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "AXIOM"
        | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
      let axs ← Lean.collectAxioms n
      let bad := axs.toList.filter (fun a => !standard.contains a)
      let inst := if Meta.isInstanceCore env n then " instance" else ""
      let internal := if n.isInternal then " internal" else ""
      IO.println s!"  {n} kind={kind}{inst}{internal} axioms={axs.toList} bad={bad}"
      if !bad.isEmpty then throwError m!"nonstandard axiom in {n}: {bad}"
      if kind == "AXIOM" then throwError m!"axiom declared: {n}"
  let mut mine : Array Name := #[]
  for (n, _) in env.constants.map₂.toList do
    if (`T205MReview).isPrefixOf n then mine := mine.push n
  mine := mine.qsort (fun a b => a.toString < b.toString)
  IO.println s!"REVIEWER constants={mine.size}"
  for n in mine do
    let axs ← Lean.collectAxioms n
    let bad := axs.toList.filter (fun a => !standard.contains a)
    IO.println s!"  {n} axioms={axs.toList} bad={bad}"
    if !bad.isEmpty then throwError m!"nonstandard axiom in {n}: {bad}"
  IO.println "INDEPENDENT_INVENTORY_PASS"
