import ExpRigidity

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarBieberbach

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def primitiveTerm (a u : A) (n : ℕ) : A :=
  (((n + 1).factorial : ℂ)⁻¹) • ((a * u) ^ n * u)

theorem primitiveTerm_summable (a u : A) : Summable (primitiveTerm a u) := by
  apply ((NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (a * u)).mul_left ‖u‖).of_norm_bounded
  intro n
  have hfac : (((n + 1).factorial : ℝ)⁻¹) ≤ (n.factorial : ℝ)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  calc
    ‖primitiveTerm a u n‖ = (((n + 1).factorial : ℝ)⁻¹) * ‖(a * u) ^ n * u‖ := by
      simp only [primitiveTerm, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (((n + 1).factorial : ℝ)⁻¹) * (‖(a * u) ^ n‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
    _ ≤ ((n.factorial : ℝ)⁻¹) * (‖(a * u) ^ n‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = ‖u‖ * ‖((n.factorial : ℂ)⁻¹) • (a * u) ^ n‖ := by
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      ring

def entireMap (a u : A) : A := ∑' n : ℕ, primitiveTerm a u n

theorem entireMap_exp_identity (a u : A) :
    a * entireMap a u = NormedSpace.exp (a * u) - 1 := by
  have hmul := (primitiveTerm_summable a u).hasSum.mul_left a
  have hexp := (hasSum_nat_add_iff' 1).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (a * u))
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, one_smul] at hexp
  have ht : (fun n => a * primitiveTerm a u n) =
      (fun n => (((n + 1).factorial : ℂ)⁻¹) • (a * u) ^ (n + 1)) := by
    funext n
    simp only [primitiveTerm, mul_smul_comm, pow_succ]
    congr 1
    ring
  rw [ht] at hmul
  exact hmul.unique hexp

def coefficient (a : A) (n : ℕ) : A :=
  if n = 0 then 0 else ((n.factorial : ℂ)⁻¹) • a ^ (n - 1)

omit [CompleteSpace A] in
theorem coefficient_term (a u : A) (n : ℕ) :
    coefficient a (n + 1) * u ^ (n + 1) = primitiveTerm a u n := by
  simp only [coefficient, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, primitiveTerm, smul_mul_assoc, mul_pow, pow_succ]
  congr 1
  ring

theorem source_series_hasSum (a u : A) :
    HasSum (fun n => coefficient a (n + 2) * u ^ (n + 2)) (entireMap a u - u) := by
  have h := (hasSum_nat_add_iff' 1).mpr (primitiveTerm_summable a u).hasSum
  have hz : primitiveTerm a u 0 = u := by simp [primitiveTerm]
  have h' : HasSum (fun n => primitiveTerm a u (n + 1)) (entireMap a u - u) := by
    simpa only [Finset.range_one, Finset.sum_singleton, hz, entireMap] using h
  simpa only [← coefficient_term, Nat.add_assoc, Nat.reduceAdd] using h'

omit [CompleteSpace A] in
theorem derivative_term (a u : A) (n : ℕ) :
    (n + 2 : ℂ) • (coefficient a (n + 2) * u ^ (n + 1)) =
      (((n + 1).factorial : ℂ)⁻¹) • (a * u) ^ (n + 1) := by
  have hn : n + 2 ≠ 0 := by omega
  have hs : n + 2 - 1 = n + 1 := by omega
  have hf : ((n + 2).factorial : ℂ) = (n + 2 : ℂ) * ((n + 1).factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hne : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [coefficient, ite_eq_right hn, hs, smul_mul_assoc, smul_smul, mul_pow, hf]
  rw [mul_inv_rev]
  congr 1
  field_simp

theorem derivative_series_summable (a u : A) :
    Summable (fun n : ℕ => (n + 2 : ℂ) • (coefficient a (n + 2) * u ^ (n + 1))) := by
  simp only [derivative_term]
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (a * u) ^ n) 1).mpr
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (a * u))

end CStarBieberbach
