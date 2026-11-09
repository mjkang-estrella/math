module
public import URMatchingAvoidanceCount
@[expose] public section
namespace URMatching
open scoped Classical
theorem local_descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ Finset.range k, (n-i)
  | 0 => rfl
  | k+1 => by rw [Nat.descFactorial, Finset.prod_range_succ_comm, local_descFactorial_eq_prod_range n k]

theorem avoidance_product_bound_reduced (N b a : ℕ) (hab : a ≤ N - b)
    (hb : b ≤ N) (hquarter : N ≤ 4 * b) :
    4 ^ a * (∏ i ∈ Finset.range a, (N - b - i)) ≤
      3 ^ a * (∏ i ∈ Finset.range a, (N - i)) := by
  have hf : ∀ i ∈ Finset.range a, 4 * (N - b - i) ≤ 3 * (N - i) := by
    intro i hi
    have hi' : i < a := Finset.mem_range.mp hi
    have hbi : b + i ≤ N := by omega
    have hni : i ≤ N := by omega
    have e₁ : N - b - i + b + i = N := by omega
    have e₂ : N - i + i = N := by omega
    omega
  have hp (k : ℕ) :
      (∀ i < k, 4 * (N-b-i) ≤ 3 * (N-i)) →
      (∏ i ∈ Finset.range k, 4 * (N-b-i)) ≤ (∏ i ∈ Finset.range k, 3 * (N-i)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro hh
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact Nat.mul_le_mul (ih (fun i hi => hh i (Nat.lt_succ_of_lt hi))) (hh k (Nat.lt_succ_self k))
  have h := hp a (fun i hi => hf i (Finset.mem_range.mpr hi))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] using h

/-- Actual one-permutation avoidance bound; all denominators cleared. -/
theorem one_colour_avoidance_bound {N : ℕ} (A B : Finset (Fin N))
    (hab : A.card ≤ N - B.card) (hb : N ≤ 4 * B.card) :
    4 ^ A.card * Fintype.card {σ : Equiv.Perm (Fin N) // AvoidsRectangle A B σ} ≤
      3 ^ A.card * N.factorial := by
  classical
  have hbN : B.card ≤ N := by simpa using B.card_le_univ
  have haN : A.card ≤ N := by simpa using A.card_le_univ
  have h := avoidance_product_bound_reduced N B.card A.card hab hbN hb
  rw [← local_descFactorial_eq_prod_range, ← local_descFactorial_eq_prod_range] at h
  rw [one_colour_avoidance_count]
  have hh := Nat.mul_le_mul_right (N - A.card).factorial h
  have he : N.descFactorial A.card * (N - A.card).factorial = N.factorial := by
    rw [Nat.mul_comm, Nat.factorial_mul_descFactorial haN]
  simpa only [Nat.mul_assoc, he] using hh

/-- The fixed rectangle bound on the actual unconditioned 100-permutation space. -/
theorem hundred_colour_avoidance_bound {N : ℕ} (A B : Finset (Fin N))
    (hab : A.card ≤ N - B.card) (hb : N ≤ 4 * B.card) :
    (4 ^ A.card) ^ 100 *
      Fintype.card {f : PermutationTuples N 100 // ∀ c, AvoidsRectangle A B (f c)} ≤
      (3 ^ A.card) ^ 100 * N.factorial ^ 100 := by
  classical
  rw [hundred_color_avoidance_count]
  simpa only [Nat.mul_pow] using
    (Nat.pow_le_pow_left (one_colour_avoidance_bound A B hab hb) 100)
end URMatching
