import PolynomialConvexity.Model

set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open Finset

/-- Descending coordinates from positive gaps, with the last gap above zero. -/
def tailSum {d : ℕ} (u : Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑ j ∈ univ.filter (i ≤ ·), u j

theorem tailSum_nonneg {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0 ≤ u j) (i : Fin d) :
    0 ≤ tailSum u i := sum_nonneg fun j _ => hu j

theorem tailSum_antitone {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0 ≤ u j) :
    Antitone (tailSum u) := by
  intro i k hik
  exact sum_le_sum_of_subset_of_nonneg
    (fun j hj => mem_filter.mpr ⟨mem_univ _, hik.trans (mem_filter.mp hj).2⟩)
    (fun j _ _ => hu j)

theorem tailSum_pos {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0 < u j) (i : Fin d) :
    0 < tailSum u i := by
  exact lt_of_lt_of_le (hu i) (single_le_sum (fun j _ => (hu j).le)
    (mem_filter.mpr ⟨mem_univ _, le_rfl⟩))

/-- The concrete maximum is the tail at the first edge containing the vertex. -/
theorem vertexThreshold_tailSum {n L d : ℕ} (e : Fin d → Edge n L)
    (u : Fin d → ℝ) (hu : ∀ j, 0 ≤ u j) (v : Fin n) :
    vertexThreshold e (tailSum u) v =
      ∑ j, if v ∈ prefixUnion e j then u j else 0 := by
  let s := univ.filter (fun i => v ∈ (e i).val)
  by_cases hs : s.Nonempty
  · let k := s.min' hs
    have hk : v ∈ (e k).val := (mem_filter.mp (min'_mem s hs)).2
    have hfirst (i : Fin d) (hi : v ∈ (e i).val) : k ≤ i :=
      min'_le s i (mem_filter.mpr ⟨mem_univ _, hi⟩)
    have hprefix (j : Fin d) : v ∈ prefixUnion e j ↔ k ≤ j := by
      rw [mem_prefixUnion]
      exact ⟨fun ⟨i, hij, hi⟩ => (hfirst i hi).trans hij,
        fun h => ⟨k, h, hk⟩⟩
    have hmax : vertexThreshold e (tailSum u) v = tailSum u k := by
      apply le_antisymm
      · exact (vertexThreshold_le e _ v _).mpr
          ⟨tailSum_nonneg u hu k, fun i hi => tailSum_antitone u hu (hfirst i hi)⟩
      · have h := (vertexThreshold_le e (tailSum u) v _).mp le_rfl
        exact h.2 k hk
    rw [hmax]
    simp_rw [hprefix]
    exact (sum_filter _ _)
  · have hv (i : Fin d) : v ∉ (e i).val := by
      intro hi
      exact hs ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have hp (j : Fin d) : v ∉ prefixUnion e j := by
      rw [mem_prefixUnion]
      rintro ⟨i, _, hi⟩
      exact hv i hi
    simp only [hp, ↓reduceIte, sum_const_zero]
    apply le_antisymm
    · exact (vertexThreshold_le e _ v 0).mpr ⟨le_rfl, fun i hi => (hv i hi).elim⟩
    · exact ((vertexThreshold_le e _ v _).mp le_rfl).1

/-- Exact prefix exponent identity for the actual descending gap map. -/
theorem prefix_exponent {n L d : ℕ} (e : Fin d → Edge n L)
    (u : Fin d → ℝ) (hu : ∀ j, 0 ≤ u j) :
    (∑ v, vertexThreshold e (tailSum u) v) =
      ∑ j, ((prefixUnion e j).card : ℝ) * u j := by
  simp_rw [vertexThreshold_tailSum e u hu]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← sum_filter]
  simp


theorem tailSum_strictAnti {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0 < u j) :
    StrictAnti (tailSum u) := by
  intro i k hik
  simp only [tailSum, sum_filter]
  apply sum_lt_sum
  · intro j _
    by_cases hk : k ≤ j
    · simp only [hk, hik.le.trans hk, ↓reduceIte, le_refl]
    · simp only [hk, ↓reduceIte]
      split_ifs
      · exact (hu j).le
      · exact le_rfl
  · exact ⟨i, mem_univ _, by simp [not_le.mpr hik, (hu i)]⟩

/-- Forward labelled descending-gap map. -/
def labelledGap {d : ℕ} (σ : Equiv.Perm (Fin d)) (u : Fin d → ℝ) : Fin d → ℝ :=
  tailSum u ∘ σ.symm

theorem vertexThreshold_relabel {n L d : ℕ} (e : Fin d → Edge n L)
    (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (v : Fin n) :
    vertexThreshold e (s ∘ σ.symm) v = vertexThreshold (tuplePerm σ e) s v := by
  apply le_antisymm
  · apply (vertexThreshold_le _ _ _ _).mpr
    have h := (vertexThreshold_le (tuplePerm σ e) s v _).mp le_rfl
    refine ⟨h.1, fun i hi => ?_⟩
    exact h.2 (σ.symm i) (by simpa [tuplePerm] using hi)
  · apply (vertexThreshold_le _ _ _ _).mpr
    have h := (vertexThreshold_le e (s ∘ σ.symm) v _).mp le_rfl
    refine ⟨h.1, fun i hi => ?_⟩
    simpa using h.2 (σ i) hi

theorem labelled_prefix_exponent {n L d : ℕ} (e : Fin d → Edge n L)
    (σ : Equiv.Perm (Fin d)) (u : Fin d → ℝ) (hu : ∀ j, 0 ≤ u j) :
    (∑ v, vertexThreshold e (labelledGap σ u) v) =
      ∑ j, ((prefixUnion (tuplePerm σ e) j).card : ℝ) * u j := by
  simp only [labelledGap, vertexThreshold_relabel]
  exact prefix_exponent _ u hu

end
end PolynomialConvexity
