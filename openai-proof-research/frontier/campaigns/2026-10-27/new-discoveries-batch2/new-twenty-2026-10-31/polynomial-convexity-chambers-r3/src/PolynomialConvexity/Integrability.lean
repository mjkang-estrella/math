import PolynomialConvexity.Moments
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace PolynomialConvexity
noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter

theorem clock_power_integrable (n k : ℕ) (v : Fin n) :
    Integrable (fun ω : Fin n → ℝ => ω v ^ k) (clockMeasure n) := by
  exact (measurePreserving_eval (fun _ : Fin n => expMeasure 1) v).integrable_comp_of_integrable
    (expOne_power_integrable k)

theorem clock_power_integral (n k : ℕ) (v : Fin n) :
    (∫ ω : Fin n → ℝ, ω v ^ k ∂clockMeasure n) = (Nat.factorial k : ℝ) := by
  have hm := (measurePreserving_eval (fun _ : Fin n => expMeasure 1) v).map_eq
  calc
    _ = ∫ t : ℝ, t ^ k ∂Measure.map (Function.eval v) (clockMeasure n) :=
      (integral_map (μ := clockMeasure n) (φ := Function.eval v) (f := fun t : ℝ => t^k) (measurable_pi_apply v).aemeasurable
        (measurable_id.pow_const k).aestronglyMeasurable).symm
    _ = ∫ t : ℝ, t ^ k ∂expMeasure 1 := by rw [clockMeasure, hm]
    _ = _ := expOne_power_integral k

theorem clock_memLp (n k : ℕ) (v : Fin n) :
    MemLp (fun ω : Fin n → ℝ => ω v) (k + 1 : ℕ) (clockMeasure n) := by
  rw [← integrable_norm_rpow_iff (measurable_pi_apply v).aestronglyMeasurable
    (by simp) (by simp)]
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using
    (clock_power_integrable n (k+1) v).congr
      ((clocks_nonneg n).mono fun ω hω => by rw [Real.norm_eq_abs, abs_of_nonneg (hω v)])

def clockSum {n : ℕ} (ω : Fin n → ℝ) : ℝ := ∑ v, ω v

theorem clockSum_memLp (n k : ℕ) :
    MemLp (clockSum (n := n)) (k + 1 : ℕ) (clockMeasure n) := by
  exact memLp_finsetSum univ (fun v _ => clock_memLp n k v)

theorem lifetime_memLp {n L : ℕ} (hL : 0 < L) (e : Edge n L) (k : ℕ) :
    MemLp (lifetime hL e) (k + 1 : ℕ) (clockMeasure n) := by
  obtain ⟨v, hv⟩ := edge_nonempty hL e
  apply (clock_memLp n k v).mono' (lifetime_measurable hL e).aestronglyMeasurable
  filter_upwards [clocks_nonneg n] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (lifetime_nonneg hL e ω hω)]
  exact lifetime_le_clock hL e ω v hv

theorem linearForm_memLp {n L : ℕ} (hL : 0 < L) (x : Edge n L → ℝ) (k : ℕ) :
    MemLp (fun ω => linearForm (fun e => lifetime hL e ω) x)
      (k + 1 : ℕ) (clockMeasure n) := by
  exact memLp_finsetSum univ (fun e _ => (lifetime_memLp hL e k).const_mul (x e))

theorem linearForm_power_integrable {n L : ℕ} (hL : 0 < L)
    (x : Edge n L → ℝ) (d : ℕ) :
    Integrable (fun ω => linearForm (fun e => lifetime hL e ω) x ^ d) (clockMeasure n) := by
  cases d with
  | zero => simp
  | succ k =>
    have h := linearForm_memLp hL x k
    apply (integrable_norm_iff (h.aestronglyMeasurable.pow (k+1))).mp
    simpa only [Pi.pow_apply, norm_pow] using h.integrable_norm_pow'

theorem clockSum_power_integrable (n d : ℕ) :
    Integrable (fun ω => clockSum (n := n) ω ^ d) (clockMeasure n) := by
  cases d with
  | zero => simp
  | succ k =>
    have h := clockSum_memLp n k
    apply (integrable_norm_iff (h.aestronglyMeasurable.pow (k+1))).mp
    simpa only [Pi.pow_apply, norm_pow] using h.integrable_norm_pow'

theorem clockSum_nonneg {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ v, 0 ≤ ω v) :
    0 ≤ clockSum ω := Finset.sum_nonneg (fun v _ => hω v)

theorem lifetime_le_clockSum {n L : ℕ} (hL : 0 < L) (e : Edge n L)
    (ω : Fin n → ℝ) (hω : ∀ v, 0 ≤ ω v) : lifetime hL e ω ≤ clockSum ω := by
  obtain ⟨v, hv⟩ := edge_nonempty hL e
  exact (lifetime_le_clock hL e ω v hv).trans
    (Finset.single_le_sum (fun w _ => hω w) (Finset.mem_univ v))

theorem mixed_power_integrable {n L d : ℕ} (hL : 0 < L)
    (e : Fin d → Edge n L) (k : ℕ) :
    Integrable (fun ω => (∏ i, lifetime hL (e i) ω) ^ k) (clockMeasure n) := by
  apply (clockSum_power_integrable n (d*k)).mono'
    (((Finset.measurable_prod univ (fun i _ => lifetime_measurable hL (e i))).pow_const k).aestronglyMeasurable)
  filter_upwards [clocks_nonneg n] with ω hω
  have hprod : 0 ≤ ∏ i, lifetime hL (e i) ω :=
    Finset.prod_nonneg (fun i _ => lifetime_nonneg hL (e i) ω hω)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hprod k), pow_mul]
  apply pow_le_pow_left₀ hprod
  calc
    _ ≤ ∏ _ : Fin d, clockSum ω := Finset.prod_le_prod₀
      (fun i _ => lifetime_nonneg hL (e i) ω hω)
      (fun i _ => lifetime_le_clockSum hL (e i) ω hω)
    _ = _ := by simp

theorem mixed_integrable {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L) :
    Integrable (fun ω => ∏ i, lifetime hL (e i) ω) (clockMeasure n) := by
  simpa only [pow_one] using mixed_power_integrable hL e 1

theorem integrated_expansion {n L : ℕ} (hL : 0 < L) (d : ℕ) (x : Edge n L → ℝ) :
    (∫ ω, linearForm (fun e => lifetime hL e ω) x ^ d ∂clockMeasure n) =
      ∑ e : Fin d → Edge n L, weight x e *
        ∫ ω, ∏ i, lifetime hL (e i) ω ∂clockMeasure n := by
  simp_rw [power_linearForm_expand]
  rw [integral_finsetSum univ (fun e _ => (mixed_integrable hL e).const_mul (weight x e))]
  simp only [integral_const_mul]

theorem concrete_integral_convex {n L : ℕ} (hL : 0 < L) (d : ℕ) :
    ConvexOn ℝ (orthant n L)
      (fun x => ∫ ω, linearForm (fun e => lifetime hL e ω) x ^ d ∂clockMeasure n) := by
  refine ⟨orthant_convex n L, ?_⟩
  intro x hx y hy a b ha hb hab
  have hi := linearForm_power_integrable hL (a • x + b • y) d
  have hj := ((linearForm_power_integrable hL x d).const_mul a).add
    ((linearForm_power_integrable hL y d).const_mul b)
  have hle := integral_mono_ae hi hj ((clocks_nonneg n).mono (fun ω hω =>
    (power_linearForm_convex d (fun e => lifetime hL e ω)
      (fun e => lifetime_nonneg hL e ω hω)).2 hx hy ha hb hab))
  simpa only [Pi.add_apply, integral_add ((linearForm_power_integrable hL x d).const_mul a)
    ((linearForm_power_integrable hL y d).const_mul b), integral_const_mul, smul_eq_mul] using hle

end
end PolynomialConvexity
