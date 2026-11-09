import ShoeBlock

namespace Shoe
open MeasureTheory
open scoped ENNReal

noncomputable def isolatedRestriction (a b i j : ℕ) : Set ℕ :=
  if j = 2*a ∨ j = 2*b+1 then {i} else {i}ᶜ

theorem isolated_eq_cylinder {K a b i : ℕ} (ha : a < K) (hb : b < K) :
    {ω : Sample ℕ | Isolated ω K a b i} =
      Set.pi (Finset.range (2*K) : Set ℕ) (isolatedRestriction a b i) := by
  classical
  ext ω
  constructor
  · intro h j hj
    have hj' : j < 2*K := Finset.mem_range.mp hj
    by_cases he : j = 2*a ∨ j = 2*b+1
    · simp only [isolatedRestriction, ite_eq_left he, Set.mem_singleton_iff]
      rcases he with rfl | rfl
      · exact h.2.2.1
      · exact h.2.2.2.1
    · simp only [isolatedRestriction, ite_eq_right he, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      have hp : j = 2*(j/2) ∨ j = 2*(j/2)+1 := by omega
      rcases hp with hp | hp
      · have hc : j/2 < K := by omega
        have hca : j/2 ≠ a := by omega
        simpa only [← hp] using h.2.2.2.2.1 (j/2) hc hca
      · have hd : j/2 < K := by omega
        have hdb : j/2 ≠ b := by omega
        simpa only [← hp] using h.2.2.2.2.2 (j/2) hd hdb
  · intro h
    refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
    · have hx := h (2*a) (Finset.mem_range.mpr (by omega))
      simpa [isolatedRestriction] using hx
    · have hx := h (2*b+1) (Finset.mem_range.mpr (by omega))
      simpa [isolatedRestriction] using hx
    · intro c hc hca
      have hx := h (2*c) (Finset.mem_range.mpr (by omega))
      have he : ¬ (2*c = 2*a ∨ 2*c = 2*b+1) := by omega
      simpa only [isolatedRestriction, ite_eq_right he, Set.mem_compl_iff,
        Set.mem_singleton_iff] using hx
    · intro d hd hdb
      have hx := h (2*d+1) (Finset.mem_range.mpr (by omega))
      have he : ¬ (2*d+1 = 2*a ∨ 2*d+1 = 2*b+1) := by omega
      simpa only [isolatedRestriction, ite_eq_right he, Set.mem_compl_iff,
        Set.mem_singleton_iff] using hx

/-- Exact finite-cylinder probability for the actual isolated block event. -/
theorem isolated_probability_product (p : DiscreteLaw ℕ) {K a b i : ℕ}
    (ha : a < K) (hb : b < K) :
    sampleMeasure p {ω | Isolated ω K a b i} =
      ∏ j ∈ Finset.range (2*K), p.toMeasure (isolatedRestriction a b i j) := by
  rw [isolated_eq_cylinder ha hb]
  apply cylinder_probability
  intro j _
  unfold isolatedRestriction
  split
  · exact measurableSet_singleton i
  · exact (measurableSet_singleton i).compl


theorem isolated_probability (p : DiscreteLaw ℕ) {K a b i : ℕ}
    (ha : a < K) (hb : b < K) :
    sampleMeasure p {ω | Isolated ω K a b i} =
      p i * p i * (1-p i)^(2*K-2) := by
  classical
  let s := Finset.range (2*K)
  let f := fun j => p.toMeasure (isolatedRestriction a b i j)
  have hA : 2*a ∈ s := Finset.mem_range.mpr (by omega)
  have hB : 2*b+1 ∈ s.erase (2*a) := by
    simp only [Finset.mem_erase, s, Finset.mem_range]
    omega
  have hsingle : p.toMeasure ({i} : Set ℕ) = p i :=
    p.toMeasure_apply_singleton i (measurableSet_singleton i)
  have hcompl : p.toMeasure ({i}ᶜ : Set ℕ) = 1-p i := by
    rw [measure_compl (measurableSet_singleton i) (measure_ne_top _ _),
      measure_univ, hsingle]
  have hfa : f (2*a) = p i := by simp [f, isolatedRestriction, hsingle]
  have hfb : f (2*b+1) = p i := by simp [f, isolatedRestriction, hsingle]
  have hrest : ∏ j ∈ (s.erase (2*a)).erase (2*b+1), f j =
      (1-p i)^(2*K-2) := by
    calc
      _ = ∏ _j ∈ (s.erase (2*a)).erase (2*b+1), (1-p i) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hmem := Finset.mem_erase.mp hj
        have hmem' := Finset.mem_erase.mp hmem.2
        have he : ¬ (j = 2*a ∨ j = 2*b+1) := by omega
        simp only [f, isolatedRestriction, ite_eq_right he, hcompl]
      _ = (1-p i)^((2*K-1)-1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem hB,
          Finset.card_erase_of_mem hA, Finset.card_range]
      _ = _ := by congr 1
  rw [isolated_probability_product p ha hb]
  change (∏ j ∈ s, f j) = _
  rw [← Finset.mul_prod_erase s f hA,
    ← Finset.mul_prod_erase (s.erase (2*a)) f hB, hfa, hfb, hrest,
    mul_assoc]

end Shoe
