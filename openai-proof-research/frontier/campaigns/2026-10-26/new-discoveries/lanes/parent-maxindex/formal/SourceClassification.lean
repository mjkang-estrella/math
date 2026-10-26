import Sharpness
import Reindexing

open scoped BigOperators

namespace MaxIndex

theorem source_next_index_counterexample (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : Fin d → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      (d : ℝ) < sortedTopSum (arithmeticEntry p) (2 * d - 4) +
        sortedTopSum (geometricEntry p) (2 * d - 4) := by
  classical
  let m := d - 3
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hdm : d = m + 3 := by dsimp [m]; omega
  let e : Fin d ≃ WitnessIndex m := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, WitnessIndex, Fintype.card_option, Fintype.card_sum,
      Fintype.card_bool]
    omega)
  let p : Fin d → ℝ := witnessProbability m ∘ e
  have hp : ∀ i, 0 ≤ p i := fun i => witnessProbability_nonneg m hm (e i)
  have hsum : ∑ i, p i = 1 := by
    change (∑ i, witnessProbability m (e i)) = 1
    rw [e.sum_comp]
    exact witnessProbability_sum m hm
  refine ⟨p, hp, hsum, ?_⟩
  have hk : 2 * d - 4 ≤ Fintype.card (Fin d × Fin d) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have : 2 * d - 4 ≤ 2 * d := Nat.sub_le _ _
    nlinarith
  rw [sortedTopSum_eq_maskTopSum (arithmeticEntry p) (fun a =>
      div_nonneg (add_nonneg (hp a.1) (hp a.2)) (by norm_num)) _ hk,
    sortedTopSum_eq_maskTopSum _ (geometricEntry_nonneg p) _ hk]
  have ha : maskTopSum (arithmeticEntry p) (2 * d - 4) =
      maskTopSum (arithmeticEntry (witnessProbability m)) (2 * d - 4) := by
    exact maskTopSum_comp_equiv (e.prodCongr e) (arithmeticEntry (witnessProbability m)) _
  have hg : maskTopSum (geometricEntry p) (2 * d - 4) =
      maskTopSum (geometricEntry (witnessProbability m)) (2 * d - 4) := by
    exact maskTopSum_comp_equiv (e.prodCongr e) (geometricEntry (witnessProbability m)) _
  have hk' : 2 * d - 4 = 2 * m + 2 := by omega
  rw [ha, hg, hk']
  have h := witness_next_index_fails m hm
  have hdreal : (d : ℝ) = (m : ℝ) + 3 := by exact_mod_cast hdm
  linarith

/-- Full classification of all allowable indices in every dimension at least five.
Both arrays are formed from the same probability vector and sorted independently. -/
theorem source_index_classification (d : ℕ) (hd : 5 ≤ d) (k : ℕ) (hk : k ≤ d * d) :
    (∀ p : Fin d → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      sortedTopSum (arithmeticEntry p) k + sortedTopSum (geometricEntry p) k ≤ (d : ℝ)) ↔
      k ≤ 2 * d - 5 := by
  have hkcard : k ≤ Fintype.card (Fin d × Fin d) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hk
  have hindex : 2 * d - 5 ≤ Fintype.card (Fin d × Fin d) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have : 2 * d - 5 ≤ 2 * d := Nat.sub_le _ _
    nlinarith
  constructor
  · intro h
    by_contra hnot
    have hnext : 2 * d - 4 ≤ k := by omega
    obtain ⟨p, hp, hsum, hfail⟩ := source_next_index_counterexample d hd
    have ha := sortedTopSum_mono (arithmeticEntry p)
      (fun a => div_nonneg (add_nonneg (hp a.1) (hp a.2)) (by norm_num)) hnext hkcard
    have hg := sortedTopSum_mono (geometricEntry p) (geometricEntry_nonneg p) hnext hkcard
    linarith [h p hp hsum]
  · intro hki p hp hsum
    have ha := sortedTopSum_mono (arithmeticEntry p)
      (fun a => div_nonneg (add_nonneg (hp a.1) (hp a.2)) (by norm_num)) hki hindex
    have hg := sortedTopSum_mono (geometricEntry p) (geometricEntry_nonneg p) hki hindex
    linarith [source_universal_index d (by omega) p hp hsum]

end MaxIndex
