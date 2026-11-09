import EntropyBound

set_option autoImplicit false

noncomputable section
open Set

namespace ArcsinhPositive

def expKernel (a p : ℝ) : ℝ := Real.exp (-Real.log (1 + Real.exp (a * p)) / p)

theorem hasDerivAt_logKernel (a : ℝ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun q ↦ -Real.log (1 + Real.exp (a * q)) / q)
      (entropyExpression (Real.exp (a * p)) / p ^ 2) p := by
  have he : HasDerivAt (fun q : ℝ ↦ Real.exp (a * q))
      (a * Real.exp (a * p)) p := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id p).const_mul a).exp
  have hd := (((he.const_add 1).log (by positivity)).neg).div (hasDerivAt_id p) hp
  convert hd using 1
  · rfl
  · dsimp [entropyExpression]
    rw [Real.log_exp]
    ring

theorem hasDerivAt_expKernel (a : ℝ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (expKernel a)
      (expKernel a p * entropyExpression (Real.exp (a * p)) / p ^ 2) p := by
  convert (hasDerivAt_logKernel a hp).exp using 1
  · rfl
  · dsimp [expKernel]
    ring

theorem hasDerivAt_entropyExpression {u : ℝ} (hu : 0 < u) :
    HasDerivAt entropyExpression (-Real.log u / (1 + u) ^ 2) u := by
  have hd : 1 + u ≠ 0 := ne_of_gt (by positivity)
  have h1 := ((hasDerivAt_id u).const_add 1).log hd
  have h2 := ((hasDerivAt_id u).mul (Real.hasDerivAt_log (ne_of_gt hu))).div
    ((hasDerivAt_id u).const_add 1) hd
  convert h1.sub h2 using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_entropy_exp (a : ℝ) (p : ℝ) :
    HasDerivAt (fun q ↦ entropyExpression (Real.exp (a * q)))
      (-p * a ^ 2 * Real.exp (a * p) / (1 + Real.exp (a * p)) ^ 2) p := by
  have he := ((hasDerivAt_id p).const_mul a).exp
  have hd := (hasDerivAt_entropyExpression (Real.exp_pos (a * p))).comp p he
  convert hd using 1
  · rfl
  · simp only [Real.log_exp, id_eq, mul_one]
    ring

def kernelDerivative (a p : ℝ) : ℝ :=
  expKernel a p * entropyExpression (Real.exp (a * p)) / p ^ 2

theorem hasDerivAt_kernelDerivative (a : ℝ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (kernelDerivative a)
      (expKernel a p / p ^ 4 *
        ((entropyExpression (Real.exp (a * p))) ^ 2 -
          2 * p * entropyExpression (Real.exp (a * p)) -
          p ^ 3 * a ^ 2 * Real.exp (a * p) / (1 + Real.exp (a * p)) ^ 2)) p := by
  have hd := ((hasDerivAt_expKernel a hp).mul (hasDerivAt_entropy_exp a p)).div
    ((hasDerivAt_id p).pow 2) (pow_ne_zero 2 hp)
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    ring

end ArcsinhPositive
