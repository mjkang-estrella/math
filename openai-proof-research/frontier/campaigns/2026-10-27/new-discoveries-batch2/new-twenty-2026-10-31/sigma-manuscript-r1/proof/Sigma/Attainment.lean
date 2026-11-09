import Sigma.Identity
import Mathlib.Order.Interval.Finset.Fin

namespace Sigma365710
open Finset

theorem left_card {n a : ℕ} (ha : a < n) :
    (univ.filter (fun v : Fin n => v.val < a)).card = a := by
  have heq : univ.filter (fun v : Fin n => v.val < a) = Iio (⟨a, ha⟩ : Fin n) := by
    ext v; simp only [mem_filter, mem_univ, true_and, mem_Iio]; rfl
  rw [heq, Fin.card_Iio]

theorem completeBipartite_degree {n a : ℕ} (ha : a < n) (u : Fin n) :
    (completeBipartite n a).degree u = if u.val < a then n - a else a := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hleft := left_card ha
  by_cases hu : u.val < a
  · simp only [hu, ↓reduceIte]
    have heq : (completeBipartite n a).neighborFinset u =
        univ \ univ.filter (fun v : Fin n => v.val < a) := by
      ext v
      rw [SimpleGraph.mem_neighborFinset]
      simp [completeBipartite, hu]
    rw [heq, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hleft]
  · simp only [hu, ↓reduceIte]
    have heq : (completeBipartite n a).neighborFinset u =
        univ.filter (fun v : Fin n => v.val < a) := by
      ext v
      rw [SimpleGraph.mem_neighborFinset]
      simp [completeBipartite, hu]
      omega
    rw [heq, hleft]

theorem sum_partition {n a : ℕ} (ha : a < n) (x y : ℤ) :
    (∑ u : Fin n, if u.val < a then x else y) = (a : ℤ) * x + ((n : ℤ) - a) * y := by
  have h := sum_filter_add_sum_filter_not (s := (univ : Finset (Fin n)))
    (p := fun u => u.val < a) (f := fun u => if u.val < a then x else y)
  have hl := left_card ha
  have hr : (univ.filter (fun u : Fin n => ¬ u.val < a)).card = n - a := by
    have hh := card_filter_add_card_filter_not (p := fun u : Fin n => u.val < a) (s := univ)
    simp only [card_univ, Fintype.card_fin] at hh
    omega
  have hx : (∑ u ∈ univ.filter (fun u : Fin n => u.val < a),
      if u.val < a then x else y) = (a : ℤ) * x := by
    have heq : (∑ u ∈ univ.filter (fun u : Fin n => u.val < a),
        if u.val < a then x else y) = ∑ _u ∈ univ.filter (fun u : Fin n => u.val < a), x := by
      apply sum_congr rfl
      intro u hu
      simp only [(mem_filter.mp hu).2, ↓reduceIte]
    rw [heq, sum_const, hl, nsmul_eq_mul]
  have hy : (∑ u ∈ univ.filter (fun u : Fin n => ¬ u.val < a),
      if u.val < a then x else y) = ((n : ℤ) - a) * y := by
    have heq : (∑ u ∈ univ.filter (fun u : Fin n => ¬ u.val < a),
        if u.val < a then x else y) = ∑ _u ∈ univ.filter (fun u : Fin n => ¬ u.val < a), y := by
      apply sum_congr rfl
      intro u hu
      simp only [(mem_filter.mp hu).2, ↓reduceIte]
    rw [heq, sum_const, hr, nsmul_eq_mul, Nat.cast_sub (by omega : a ≤ n)]
  rw [← h, hx, hy]

theorem completeBipartite_sigmaT {n a : ℕ} (ha : a < n) :
    sigmaT (completeBipartite n a) = F n a := by
  rw [sigmaT, pair_variance]
  simp_rw [completeBipartite_degree ha]
  push_cast
  simp only [ite_pow]
  rw [sum_partition ha, sum_partition ha]
  rw [Nat.cast_sub (by omega : a ≤ n)]
  unfold F
  ring

/-- Attainment and maximization within the complete bipartite family only.
The universal triangle-free domination theorem is proved in Sigma.Endpoint. -/
theorem attained_family_maximum {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧
      (completeBipartite n a).Connected ∧
      (completeBipartite n a).CliqueFree 3 ∧
      sigmaT (completeBipartite n a) = F n a ∧
      ∀ b : ℕ, 1 ≤ b → b < n →
        sigmaT (completeBipartite n b) ≤ sigmaT (completeBipartite n a) := by
  obtain ⟨a, ha, han, hmax⟩ := exists_maximizing_part hn
  refine ⟨a, ha, han, completeBipartite_connected ha han,
    completeBipartite_cliqueFree n a, completeBipartite_sigmaT han, ?_⟩
  intro b hb hbn
  rw [completeBipartite_sigmaT hbn, completeBipartite_sigmaT han]
  exact hmax b hb hbn

end Sigma365710
