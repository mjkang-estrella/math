module
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

/-- Literal modified Bessel Gamma-series summand. -/
@[expose] def term (ν z : ℝ) (k : ℕ) : ℝ :=
  (z / 2) ^ ((2 * k : ℕ) + ν) / ((k.factorial : ℝ) * Real.Gamma (k + ν + 1))
/-- Literal positive-axis source function, not an ODE surrogate. -/
@[expose] def I (ν z : ℝ) : ℝ := ∑' k : ℕ, term ν z k
/-- Gamma-normalized coefficients (the Gamma factor at zero is retained). -/
@[expose] def coeff (ν : ℝ) (k : ℕ) : ℝ :=
  1 / ((4 : ℝ)^k * (k.factorial : ℝ) * Real.Gamma (k + ν + 1))
@[expose] def S (ν t : ℝ) : ℝ := ∑' k : ℕ, coeff ν k * t^k
/-- Normalized series with constant term one for ν > -1. -/
@[expose] def F (ν t : ℝ) : ℝ := Real.Gamma (ν + 1) * S ν t

theorem gamma_pos {ν : ℝ} (hν : -1 < ν) (k : ℕ) :
    0 < Real.Gamma (k + ν + 1) := by
  apply Real.Gamma_pos_of_pos
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem coeff_pos {ν : ℝ} (hν : -1 < ν) (k : ℕ) : 0 < coeff ν k := by
  unfold coeff
  positivity [gamma_pos hν k]

theorem coeff_succ {ν : ℝ} (hν : -1 < ν) (k : ℕ) :
    coeff ν (k+1) = coeff ν k / (4 * (k+1) * (k+ν+1)) := by
  have hg := gamma_pos hν k
  have hp : (k : ℝ) + ν + 1 ≠ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  unfold coeff
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show (k : ℝ) + 1 + ν + 1 = (k + ν + 1) + 1 by ring,
    Real.Gamma_add_one hp]
  field_simp

theorem term_factor {ν z : ℝ} (hz : 0 < z) (k : ℕ) :
    term ν z k = (z/2)^ν * (coeff ν k * (z^2)^k) := by
  have hz' : 0 < z/2 := by positivity
  unfold term coeff
  rw [Real.rpow_add hz', Real.rpow_natCast]
  have hp : (z / 2) ^ (2 * k) = (z^2)^k / (4:ℝ)^k := by
    rw [pow_mul, div_pow]
    norm_num
    rw [div_pow]
  rw [hp]
  ring

/-- Exact literal-series identity; does not assume summability. -/
theorem I_eq_rpow_mul_S {ν z : ℝ} (hz : 0 < z) :
    I ν z = (z/2)^ν * S ν (z^2) := by
  unfold I S
  simp_rw [term_factor hz]
  exact tsum_mul_left

theorem I_eq_normalized {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    I ν z = (z/2)^ν / Real.Gamma (ν+1) * F ν (z^2) := by
  rw [I_eq_rpow_mul_S hz]
  unfold F
  have hg : Real.Gamma (ν+1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp

theorem summable_S {ν t : ℝ} (hν : -1 < ν) :
    Summable (fun k : ℕ => coeff ν k * t^k) := by
  by_cases ht : t = 0
  · subst t
    exact (hasSum_single 0 (fun k hk => by simp [hk])).summable
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Filter.Eventually.of_forall (fun k => mul_ne_zero (coeff_pos hν k).ne' (pow_ne_zero k ht))
  have heq : (fun k : ℕ => ‖coeff ν (k+1) * t^(k+1)‖ / ‖coeff ν k * t^k‖) =
      (fun k : ℕ => |t| / (4 * (k+1) * (k+ν+1))) := by
    funext k
    have hc := (coeff_pos hν k).ne'
    have hp : 0 < (k : ℝ) + ν + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    simp only [coeff_succ hν, pow_succ, norm_mul, norm_div, Real.norm_eq_abs,
      abs_of_pos (coeff_pos hν k), abs_of_pos hp, abs_of_pos (by positivity : 0 < (k:ℝ)+1),
      abs_of_pos (by norm_num : (0:ℝ)<4)]
    field_simp
  rw [heq]
  apply tendsto_const_nhds.div_atTop
  have hn : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact (tendsto_atTop_add_const_right _ 1 hn |>.const_mul_atTop (by norm_num : (0:ℝ)<4)).atTop_mul_atTop₀
    (tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_right _ ν hn))

theorem summable_term {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) :
    Summable (term ν z) := by
  simp_rw [funext (term_factor hz)]
  exact (summable_S hν).mul_left _

theorem I_pos {ν z : ℝ} (hν : -1 < ν) (hz : 0 < z) : 0 < I ν z := by
  unfold I
  apply (summable_term hν hz).tsum_pos
  · intro k
    unfold term
    exact le_of_lt (div_pos (Real.rpow_pos_of_pos (by positivity) _) (mul_pos (by positivity) (gamma_pos hν k)))
  · unfold term
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (mul_pos (by positivity) (gamma_pos hν 0))

end BesselRatio
