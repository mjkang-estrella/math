import Mathlib
set_option maxRecDepth 2000
set_option maxHeartbeats 1600000

open PowerSeries
namespace StirlingPositivity

noncomputable def tail (r : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if r ≤ n then 1 / (n.factorial : ℚ) else 0

noncomputable def shifted (r : ℕ) : PowerSeries ℚ :=
  PowerSeries.rescale (-(1 / ((r : ℚ) + 1))) (PowerSeries.exp ℚ) * tail r

lemma coeff_tail (r n : ℕ) : (tail r).coeff n =
    if r ≤ n then 1 / (n.factorial : ℚ) else 0 := by simp [tail]

lemma derivative_tail (s : ℕ) :
    PowerSeries.derivative (tail (s+1)) =
      tail (s+1) + PowerSeries.monomial s (1/(s.factorial:ℚ)) := by
  ext n
  rw [PowerSeries.coeff_derivative, map_add, coeff_tail, coeff_tail,
    PowerSeries.coeff_monomial]
  by_cases h : n=s
  · subst n
    have hn : (s:ℚ)+1 ≠ 0 := by positivity
    simp [Nat.factorial_succ]
    field_simp
  · by_cases hsn : s+1 ≤ n
    · have hs : s+1 ≤ n+1 := by omega
      simp only [hsn, hs, ite_true, h, ite_false, add_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (n:ℚ)+1 ≠ 0 := by positivity
      field_simp
    · have hs : ¬s+1 ≤ n+1 := by omega
      simp [hsn, hs, h]

lemma derivative_rescaled_exp (a : ℚ) :
    PowerSeries.derivative (PowerSeries.rescale a (PowerSeries.exp ℚ)) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.exp ℚ) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, Algebra.algebraMap_self, RingHom.id_apply, PowerSeries.coeff_C_mul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp

lemma derivative_shifted (s : ℕ) :
    PowerSeries.derivative (shifted (s+1)) =
      PowerSeries.C (((s+1:ℕ):ℚ)/((s+1:ℕ)+1)) * shifted (s+1) +
      PowerSeries.rescale (-(1 / (((s+1:ℕ):ℚ) + 1))) (PowerSeries.exp ℚ) *
        PowerSeries.monomial s (1/(s.factorial:ℚ)) := by
  unfold shifted
  rw [PowerSeries.derivative.leibniz, derivative_rescaled_exp, derivative_tail]
  have hr : ((s+1:ℕ):ℚ)+1 ≠ 0 := by positivity
  have heq : -(1/(((s+1:ℕ):ℚ)+1))+1 = ((s+1:ℕ):ℚ)/(((s+1:ℕ):ℚ)+1) := by field_simp; ring
  rw [← heq, map_add, map_one]
  ring

lemma coeff_mul_monomial_add (f : PowerSeries ℚ) (s m : ℕ) (a : ℚ) :
    (f * PowerSeries.monomial s a).coeff (s+m) = f.coeff m * a := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc]
  simpa [Nat.add_comm] using PowerSeries.coeff_mul_X_pow (f * C a) s m

lemma coeff_shifted_rec (s m : ℕ) :
    (shifted (s+1)).coeff (s+m+1) * ((s+m:ℕ)+1:ℚ) =
      ((s+1:ℕ):ℚ)/(((s+1:ℕ):ℚ)+1) * (shifted (s+1)).coeff (s+m) +
      (-(1/(((s+1:ℕ):ℚ)+1)))^m / ((m.factorial:ℚ)*(s.factorial:ℚ)) := by
  have h := congrArg (fun f : PowerSeries ℚ => f.coeff (s+m)) (derivative_shifted s)
  rw [PowerSeries.coeff_derivative, map_add, PowerSeries.coeff_C_mul,
      coeff_mul_monomial_add] at h
  simpa [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using h

lemma coeff_shifted_lt (r n : ℕ) (h : n<r) : (shifted r).coeff n = 0 := by
  rw [shifted, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hj : ij.2<r := by omega
  simp [coeff_tail, show ¬ r ≤ ij.2 by omega]

lemma coeff_shifted_first (r : ℕ) : (shifted r).coeff r = 1/(r.factorial:ℚ) := by
  classical
  rw [shifted, PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0,r)]
  · simp [coeff_tail]
  · intro ij hij hne
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hj : ij.2<r := by
      have hne' : ij.1≠0 := by
        intro hzero
        have heq : ij=(0,r) := by apply Prod.ext <;> simp_all
        exact hne heq
      omega
    simp [coeff_tail, show ¬ r ≤ ij.2 by omega]
  · simp

noncomputable def scaled (s m : ℕ) : ℚ :=
  (shifted (s+1)).coeff (s+1+m) * ((s+1+m).factorial:ℚ) * (((s:ℚ)+2)^m)

lemma scaled_zero (s : ℕ) : scaled s 0=1 := by
  simp [scaled, coeff_shifted_first, Nat.factorial_ne_zero]

end StirlingPositivity
