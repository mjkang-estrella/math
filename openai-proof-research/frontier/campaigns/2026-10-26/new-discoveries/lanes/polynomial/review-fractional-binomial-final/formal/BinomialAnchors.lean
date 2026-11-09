import Mathlib

namespace FractionalBinomial

lemma sum_range_pairs (f : ℕ → ℝ) (n : ℕ) :
    (∑ m∈Finset.range (n*2), f m) =
      ∑ j∈Finset.range n, (f (j*2)+f (j*2+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
    simp [Finset.sum_range_succ]

/-- The classical even-binomial filter, used only as an anchor. -/
lemma even_binomial_identity (k : ℕ) (p q : ℝ) :
    (p+q)^(2*k)+(-p+q)^(2*k)=
      2*∑ j∈Finset.range (k+1), ((2*k).choose (2*j):ℝ)*p^(2*j)*q^(2*(k-j)) := by
  let f : ℕ → ℝ := fun m => (p^m+(-p)^m)*q^(2*k-m)*((2*k).choose m:ℝ)
  have hpow : (p+q)^(2*k)+(-p+q)^(2*k)=∑ m∈Finset.range (2*k+1), f m := by
    rw [add_pow, add_pow, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [f]
    ring
  have hlast : f (2*k+1)=0 := by
    dsimp [f]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  have hextra : (∑ m∈Finset.range ((k+1)*2), f m) = ∑ m∈Finset.range (2*k+1), f m := by
    rw [show (k+1)*2=(2*k+1)+1 by omega, Finset.sum_range_succ, hlast, add_zero]
  rw [← hextra, sum_range_pairs] at hpow
  rw [hpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have heven : (-p)^(j*2)=p^(j*2) := by
    rw [Nat.mul_comm j 2, pow_mul, pow_mul, neg_sq]
  have hodd : (-p)^(j*2+1)= -(p^(j*2+1)) := by
    rw [pow_succ, pow_succ, heven]
    ring
  have hsub : 2*k-j*2=2*(k-j) := by omega
  dsimp [f]
  rw [heven, hodd, add_neg_cancel, zero_mul, zero_mul, add_zero, hsub]
  rw [Nat.mul_comm j 2]
  ring

end FractionalBinomial
