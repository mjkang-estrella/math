import TraceLog

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

noncomputable def hamiltonianPolynomial (u v : n → K) (gamma : K) : Polynomial K :=
  ∑ i ∈ Finset.range (Fintype.card n),
    Polynomial.C (Matrix.trace (hamiltonianDirection u v gamma * upperKernel u v ^ i)) *
      Polynomial.X ^ (i + 1)

omit [CharZero K] in
theorem hamiltonianPolynomial_eval (u v : n → K) (gamma t : K) :
    (hamiltonianPolynomial u v gamma).eval t = hamiltonianGenerator u v gamma t := by
  rw [hamiltonianGenerator_finite_sum]
  simp only [hamiltonianPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem determinant_polynomial_collapse (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - (Polynomial.X : Polynomial K) • (algebraicLax u v lam xi).map Polynomial.C).det =
      1 - Polynomial.C lam * hamiltonianPolynomial u v gamma := by
  apply Polynomial.funext
  intro t
  have hd := det_eq_one_sub_generator u v t lam xi gamma hcurve
  rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    hamiltonianPolynomial_eval]
  change (Polynomial.evalRingHom t) _ = _
  rw [RingHom.map_det]
  convert hd using 1
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

omit [CharZero K] in
theorem hamiltonianPolynomial_constantCoeff (u v : n → K) (gamma : K) :
    PowerSeries.constantCoeff (hamiltonianPolynomial u v gamma : PowerSeries K) = 0 := by
  simp [hamiltonianPolynomial, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]


theorem determinant_series_collapse (u v : n → K) (lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - (PowerSeries.X : PowerSeries K) • (algebraicLax u v lam xi).map PowerSeries.C).det =
      1 - PowerSeries.C lam * (hamiltonianPolynomial u v gamma : PowerSeries K) := by
  have hd := congrArg (Polynomial.coeToPowerSeries.ringHom (R := K))
    (determinant_polynomial_collapse u v lam xi gamma hcurve)
  rw [RingHom.map_det] at hd
  have hm : (Polynomial.coeToPowerSeries.ringHom (R := K)).mapMatrix
      (1 - (Polynomial.X : Polynomial K) • (algebraicLax u v lam xi).map Polynomial.C) =
      1 - (PowerSeries.X : PowerSeries K) • (algebraicLax u v lam xi).map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    simp [RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Polynomial.coeToPowerSeries.ringHom_apply]
    split_ifs <;> simp [mul_comm]
  rw [hm] at hd
  simpa using hd

end PeakonCoefficients
