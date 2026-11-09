import SelectedFamily
set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
attribute [local instance] Classical.propDecidable

theorem sum_fin_cast (n m : ℕ) (h : n = m) (f : (Fin m → Bool) → ℝ) :
    (∑ v : Fin n → Bool, f (fun i => v (Fin.cast h.symm i))) = ∑ v, f v := by
  subst m
  rfl

def selectedFunction (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) : Fin (depth k) → Bool :=
  fun i => (selectedWord k u)[i.val]'(by rw [selectedWord_length k hk u]; exact i.isLt)

theorem selectedFunction_word (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    List.ofFn (selectedFunction k hk u) = selectedWord k u := by
  apply List.ext_getElem
  · simp [selectedWord_length k hk u]
  · intro i hi hj
    simp [selectedFunction]

theorem selectedFunction_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (selectedFunction k hk) := by
  intro u v he
  apply selectedWord_injective k
  simpa only [selectedFunction_word] using congrArg List.ofFn he

theorem selectedWord_weight (k : ℕ) (hk : 3 ≤ k) (u : SelectedCode k) :
    cascade sourceTree (fairAssignment sourceTree) (selectedWord k u) =
      (1/2:ℝ) ^ (depth k-1) := by
  have hl : (selectedWord k u) ≠ [] := by
    have hh := selectedWord_length k hk u
    have := index_le_depth k
    intro he; simp [he] at hh; omega
  rw [cascade_fair_halfpower sourceTree hl, selectedWord_alphaLIS k hk u,
    selectedWord_length k hk u]
  rfl

theorem selected_kappa_lower (k : ℕ) (hk : 3 ≤ k) :
    (1/2:ℝ) ^ deficit k ≤ kappa sourceTree (fairAssignment sourceTree) [true] (depth k) := by
  classical
  let f : (Fin (depth k) → Bool) → ℝ := fun v =>
    if FiniteContext sourceTree.nodes (List.ofFn v) ∧ alphaLIS sourceTree (List.ofFn v) = [true]
      then cascade sourceTree (fairAssignment sourceTree) (List.ofFn v) else 0
  have hf : ∀ v, 0 ≤ f v := by
    intro v
    dsimp [f]
    split_ifs
    · have hn : List.ofFn v ≠ [] := by
        intro he
        have hh := congrArg List.length he
        simp at hh
        have := index_le_depth k
        omega
      rw [cascade_fair sourceTree hn]
      positivity
    · exact le_rfl
  have he : ∀ u, f (selectedFunction k hk u) = (1/2:ℝ)^(depth k-1) := by
    intro u
    simp only [f, selectedFunction_word, selectedWord_context k hk u,
      selectedWord_alphaLIS k hk u, and_self, ↓reduceIte, selectedWord_weight k hk u]
  have hsum : (∑ u : SelectedCode k, f (selectedFunction k hk u)) ≤ ∑ v, f v := by
    rw [← Finset.sum_image (fun a _ b _ hab => selectedFunction_injective k hk hab)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (by intro v _ _; exact hf v)
  have hcard : (∑ u : SelectedCode k, f (selectedFunction k hk u)) =
      (2:ℝ)^(freeCount k) * (1/2:ℝ)^(depth k-1) := by
    simp only [he, Finset.sum_const, Finset.card_univ, selectedCode_card, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  have hc : (2:ℝ)^freeCount k * (1/2:ℝ)^freeCount k = 1 := by
    rw [← mul_pow]; norm_num
  have harith : (2:ℝ)^freeCount k * (1/2:ℝ)^(depth k-1) = (1/2:ℝ)^deficit k := by
    rw [← deficit_add_free k hk, pow_add]
    calc
      _ = ((2:ℝ)^freeCount k * (1/2:ℝ)^freeCount k) * (1/2:ℝ)^deficit k := by ring
      _ = _ := by rw [hc, one_mul]
  rw [hcard, harith] at hsum
  unfold kappa
  simp only [List.length_singleton, Nat.one_add, Nat.succ_sub_one]
  change _ ≤ ∑ v : Fin (1+depth k-1) → Bool,
    f (fun i => v (Fin.cast (show depth k = 1+depth k-1 by omega) i))
  rw [sum_fin_cast _ _ (by omega)]
  exact hsum

theorem fixed_kappa_not_geometric :
    ¬ GeometricDecay (kappa sourceTree (fairAssignment sourceTree) [true]) := by
  rintro ⟨C,r,hC,hr,hr1,n0,hn⟩
  obtain ⟨k,hk,hkn,hlt⟩ := depth_beats_geometric C r hC hr hr1 n0
  exact (not_lt_of_ge ((selected_kappa_lower k hk).trans (hn _ hkn))) hlt

theorem source_geometric_rate_refuted : ¬ SourceGeometricRateClaim := by
  intro h
  apply fixed_kappa_not_geometric
  exact h sourceTree (fairAssignment sourceTree) sourceTree_no_infinite_stable [true]
    one_contextAlphaLIS
end CascadeRate
