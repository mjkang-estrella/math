import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/- Original support code: Myeongjin Kang, MIT.
Finite-poset core only. No representation-theoretic theorem is asserted. -/
namespace T205M

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def IsIdeal (s : Finset α) : Prop :=
  ∀ ⦃x y : α⦄, y ∈ s → x ≤ y → x ∈ s

omit [DecidableEq α] in
theorem empty_ideal : IsIdeal (∅ : Finset α) := by
  intro x y hy
  simp at hy

theorem ideal_insert_minimal {s t : Finset α}
    (hs : IsIdeal s) (ht : IsIdeal t) (hst : s ⊆ t)
    (hlt : s.card < t.card) :
    ∃ x ∈ t, x ∉ s ∧ IsIdeal (insert x s) ∧ insert x s ⊆ t := by
  have hne : (t \ s).Nonempty := by
    by_contra h
    have hts : t ⊆ s := by
      intro x hx
      by_contra hxs
      exact h ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxs⟩⟩
    exact (Nat.not_le_of_lt hlt) (Finset.card_le_card hts)
  obtain ⟨x, hx, hmin⟩ := (t \ s).exists_minimal hne
  obtain ⟨hxt, hxs⟩ := Finset.mem_sdiff.mp hx
  refine ⟨x, hxt, hxs, ?_, Finset.insert_subset hxt hst⟩
  intro a b hb hab
  rcases Finset.mem_insert.mp hb with rfl | hbs
  · by_cases has : a ∈ s
    · exact Finset.mem_insert_of_mem has
    · have hat := ht hxt hab
      have hxa := hmin (Finset.mem_sdiff.mpr ⟨hat, has⟩) hab
      exact Finset.mem_insert.mpr (Or.inl (le_antisymm hab hxa))
  · exact Finset.mem_insert_of_mem (hs hbs hab)

theorem ideal_interval_rank {s t : Finset α}
    (hs : IsIdeal s) (ht : IsIdeal t) (hst : s ⊆ t)
    {r : ℕ} (hsr : s.card ≤ r) (hrt : r ≤ t.card) :
    ∃ u : Finset α, IsIdeal u ∧ s ⊆ u ∧ u ⊆ t ∧ u.card = r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hsr
  induction k with
  | zero => exact ⟨s, hs, Finset.Subset.refl s, hst, by omega⟩
  | succ k ih =>
    obtain ⟨u, hu, hsu, hut, huc⟩ := ih (by omega) (by omega)
    obtain ⟨x, hxt, hxu, hi, hit⟩ :=
      ideal_insert_minimal hu ht hut (by omega)
    refine ⟨insert x u, hi, ?_, hit, ?_⟩
    · exact Finset.Subset.trans hsu (Finset.subset_insert x u)
    · rw [Finset.card_insert_of_notMem hxu, huc]
      omega

theorem unique_rank_cross_comparable [Fintype α] {s : Finset α}
    (_hs : IsIdeal s)
    (hunique : ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s)
    {a b : α} (ha : a ∈ s) (hb : b ∉ s) : a ≤ b := by
  classical
  by_contra hab
  let d := Finset.univ.filter (fun x : α => x ≤ b)
  have hd : IsIdeal d := by
    intro x y hy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      le_trans hxy (Finset.mem_filter.mp hy).2⟩
  have hbd : b ∈ d := Finset.mem_filter.mpr ⟨Finset.mem_univ b, le_rfl⟩
  have had : a ∉ d := by
    intro h
    exact hab (Finset.mem_filter.mp h).2
  rcases le_total d.card s.card with hds | hsd
  · have hu : IsIdeal (Finset.univ : Finset α) := by
      intro x y _ _
      exact Finset.mem_univ x
    obtain ⟨u, hi, hdu, _, hc⟩ := ideal_interval_rank hd hu
      (Finset.subset_univ d) hds (Finset.card_le_univ s)
    have heq := hunique u hi hc
    exact hb (heq ▸ hdu hbd)
  · obtain ⟨u, hi, _, hud, hc⟩ := ideal_interval_rank empty_ideal hd
      (Finset.empty_subset d) (by simp) hsd
    have heq := hunique u hi hc
    exact had (hud (heq.symm ▸ ha))

theorem exists_second_ideal_of_incomparable [Fintype α] {s : Finset α}
    (hs : IsIdeal s) {a b : α} (ha : a ∈ s) (hb : b ∉ s)
    (hab : ¬a ≤ b) :
    ∃ t : Finset α, IsIdeal t ∧ t.card = s.card ∧ t ≠ s := by
  by_contra h
  have hu : ∀ t : Finset α, IsIdeal t → t.card = s.card → t = s := by
    intro t ht hc
    by_contra hne
    exact h ⟨t, ht, hc, hne⟩
  exact hab (unique_rank_cross_comparable hs hu ha hb)

theorem two_ideals_of_no_cut [Fintype α] {r : ℕ}
    (hr : r ≤ Fintype.card α)
    (hno : ∀ s : Finset α, IsIdeal s → s.card = r →
      ∃ a ∈ s, ∃ b ∉ s, ¬a ≤ b) :
    ∃ s t : Finset α, IsIdeal s ∧ IsIdeal t ∧
      s.card = r ∧ t.card = r ∧ s ≠ t := by
  have hu : IsIdeal (Finset.univ : Finset α) := by
    intro x y _ _
    exact Finset.mem_univ x
  obtain ⟨s, hs, _, _, hsc⟩ := ideal_interval_rank empty_ideal hu
    (Finset.empty_subset _) (r := r) (by simp) (by simpa using hr)
  obtain ⟨a, ha, b, hb, hab⟩ := hno s hs hsc
  obtain ⟨t, ht, htc, hne⟩ := exists_second_ideal_of_incomparable hs ha hb hab
  exact ⟨s, t, hs, ht, hsc, htc.trans hsc, Ne.symm hne⟩

end T205M
