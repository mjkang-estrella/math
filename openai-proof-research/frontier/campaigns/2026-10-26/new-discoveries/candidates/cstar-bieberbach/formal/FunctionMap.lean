import EntireSeries

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarBieberbach

abbrev Time := Set.Icc (0 : ℝ) 1
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩
instance : Nonempty Time := ⟨timeZero⟩
abbrev FunctionAlgebra := C(Time, ℂ)

def parameter : FunctionAlgebra :=
  ⟨fun t => (8 : ℂ) * (t : ℝ), continuous_const.mul
    (Complex.continuous_ofReal.comp continuous_subtype_val)⟩

def witnessMap (u : FunctionAlgebra) : FunctionAlgebra := entireMap parameter u

theorem exp_apply (f : FunctionAlgebra) (t : Time) :
    (NormedSpace.exp f) t = Complex.exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  change (NormedSpace.exp f) t = NormedSpace.exp (f t) at h
  rw [← Complex.exp_eq_exp_ℂ] at h
  exact h

theorem witnessMap_exp_identity (u : FunctionAlgebra) (t : Time) :
    Complex.exp (parameter t * u t) = 1 + parameter t * witnessMap u t := by
  have h := congrArg (fun f : FunctionAlgebra => f t) (entireMap_exp_identity parameter u)
  change parameter t * witnessMap u t = (NormedSpace.exp (parameter * u)) t - 1 at h
  rw [exp_apply] at h
  change parameter t * witnessMap u t = Complex.exp (parameter t * u t) - 1 at h
  linear_combination -h

theorem witnessMap_at_zero (u : FunctionAlgebra) : witnessMap u timeZero = u timeZero := by
  change (ContinuousMap.evalCLM ℂ timeZero) (∑' n, primitiveTerm parameter u n) = _
  rw [ContinuousLinearMap.map_tsum _ (primitiveTerm_summable parameter u)]
  simp [primitiveTerm, parameter, timeZero, zero_pow_eq]

theorem parameter_ne_zero (t : Time) (ht : t ≠ timeZero) : parameter t ≠ 0 := by
  change (8 : ℂ) * ((t : ℝ) : ℂ) ≠ 0
  apply mul_ne_zero (by norm_num)
  apply Complex.ofReal_ne_zero.mpr
  intro hz
  apply ht
  exact Subtype.ext hz

theorem witnessMap_injective : Function.Injective witnessMap := by
  intro u v huv
  let h : Time → ℂ := fun t => parameter t * (u t - v t)
  have hh : Continuous h := parameter.continuous.mul (u.continuous.sub v.continuous)
  have he : ∀ t, Complex.exp (h t) = 1 := by
    intro t
    change Complex.exp (parameter t * (u t - v t)) = 1
    rw [mul_sub]
    apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mp
    rw [witnessMap_exp_identity, witnessMap_exp_identity, huv]
  have h0 : h timeZero = 0 := by simp [h, parameter, timeZero]
  have hzero := continuous_exp_kernel_zero h hh he timeZero h0
  apply ContinuousMap.ext
  intro t
  by_cases ht : t = timeZero
  · subst t
    have heq := congrArg (fun f : FunctionAlgebra => f timeZero) huv
    simpa only [witnessMap_at_zero] using heq
  · have hz := hzero t
    change parameter t * (u t - v t) = 0 at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (parameter_ne_zero t ht))

end CStarBieberbach
