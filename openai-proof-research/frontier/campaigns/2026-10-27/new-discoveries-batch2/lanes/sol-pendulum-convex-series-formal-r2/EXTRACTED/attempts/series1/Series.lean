module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Convexity
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Data.Nat.Choose.Central
public section
noncomputable section
open Real MeasureTheory Set Polynomial
namespace PendulumTimeMap

theorem choose_step (r : ℝ) (n : ℕ) :
 ((n:ℝ)+1)*Ring.choose r (n+1) = (r-n)*Ring.choose r n := by
 rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right]
 simp only [smul_eq_mul, smeval_mul, smeval_sub, smeval_X, smeval_natCast,
  Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
 have h : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
 have h' : (n:ℝ)+1≠0 := by positivity
 field_simp
 ring

theorem weight_step (n : ℕ) :
 ((n:ℝ)+1)*weight (n+1) = ((2*(n:ℝ)+1)/4)*weight n := by
 have h := Nat.succ_mul_centralBinom_succ n
 have hr : ((n:ℝ)+1)*(Nat.centralBinom (n+1):ℝ) =
  2*(2*(n:ℝ)+1)*(Nat.centralBinom n:ℝ) := by exact_mod_cast h
 unfold weight
 change ((n:ℝ)+1)*((Nat.centralBinom (n+1):ℝ)/8^(n+1)) =
  ((2*(n:ℝ)+1)/4)*((Nat.centralBinom n:ℝ)/8^n)
 rw [pow_succ]
 have hp : (8:ℝ)^n≠0 := by positivity
 field_simp
 nlinarith [hr]

theorem weight_eq_choose (n : ℕ) :
 weight n = Ring.choose (-1/2:ℝ) n * (-1/2:ℝ)^n := by
 induction n with
 | zero => simp [weight]
 | succ n ih =>
  have hc := choose_step (-1/2) n
  have hw := weight_step n
  rw [ih] at hw
  rw [pow_succ]
  have hn : (n:ℝ)+1≠0 := by positivity
  apply (mul_left_cancel₀ hn)
  calc
   _ = ((2*(n:ℝ)+1)/4)*(Ring.choose (-1/2:ℝ) n * (-1/2:ℝ)^n) := hw
   _ = (((n:ℝ)+1)*Ring.choose (-1/2:ℝ) (n+1)) * (-1/2:ℝ)^n * (-1/2) := by rw [hc]; ring
   _ = _ := by ring

theorem weight_hasSum {t : ℝ} (ht : |t|<2) :
 HasSum (fun n => weight n*t^n) ((1-t/2)^(-1/2:ℝ)) := by
 have hmem : (-t/2:ℝ) ∈ Metric.eball 0 (1:ENNReal) := by
  rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
  simpa only [Real.dist_eq, sub_zero, abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<2)] using (div_lt_one (by norm_num : (0:ℝ)<2)).mpr ht
 have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1/2:ℝ))).hasSum hmem
 simpa only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul, zero_add,
  ← mul_pow, weight_eq_choose, mul_assoc, show (-1/2:ℝ)*t=-t/2 by ring,
  show (1+ -t/2:ℝ)=1-t/2 by ring] using h


theorem kernel_hasSum {a z t : ℝ} (ht : 0<t) (ht2 : t<2) (hs : 0<a+z-t) :
 HasSum (fun n => weight n*momentKernel n a z t) (Real.sqrt 2 * transformedKernel a z t) := by
 have h := (weight_hasSum (t := t) (by rwa [abs_of_pos ht])).mul_right
  ((Real.sqrt (t*(a+z-t)))⁻¹)
 have he : (1-t/2)^(-1/2:ℝ)*(Real.sqrt (t*(a+z-t)))⁻¹ =
  Real.sqrt 2 * transformedKernel a z t := by
  rw [show (-1/2:ℝ)=-(1/2) by ring, Real.rpow_neg (by linarith : 0≤1-t/2),
   ← Real.sqrt_eq_rpow, show 1-t/2=(2-t)/2 by ring, Real.sqrt_div (by linarith : 0≤2-t)]
  unfold transformedKernel
  rw [Real.sqrt_mul (mul_pos ht (by linarith : 0<2-t)).le,
   Real.sqrt_mul ht.le, Real.sqrt_mul ht.le]
  ring
 rw [he] at h
 convert h using 1
 funext n
 unfold momentKernel
 ring

theorem series_piece {a z r : ℝ} (ha : 0<a) (hz : 0<z)
 (hr : 0<r) (hr2 : r<2) (hrs : r<a+z)
 (hi : ∀ n, IntervalIntegrable (momentKernel n a z) volume 0 r)
 (ht : IntervalIntegrable (transformedKernel a z) volume 0 r) :
 HasSum (fun n => weight n * ∫ t in 0..r, momentKernel n a z t)
  (Real.sqrt 2 * ∫ t in 0..r, transformedKernel a z t) := by
 let F := fun n t => weight n*momentKernel n a z t
 have hs : ∀ t ∈ Ioc 0 r, HasSum (fun n => F n t) (Real.sqrt 2*transformedKernel a z t) := by
  intro t ht
  exact kernel_hasSum ht.1 (by linarith [ht.2]) (by linarith [ht.2])
 have hpos : ∀ n t, 0≤t → 0≤F n t := by
  intro n t ht
  exact mul_nonneg (weight_pos n).le (div_nonneg (pow_nonneg ht n) (Real.sqrt_nonneg _))
 have hiSum : IntervalIntegrable (fun t => ∑' n, F n t) volume 0 r := by
  apply (ht.const_mul (Real.sqrt 2)).congr_uIoo
  intro t ht
  rw [uIoo_of_lt hr] at ht
  exact (hs t ⟨ht.1,ht.2.le⟩).tsum_eq.symm
 have hd := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
  (a := 0) (b := r) (F := F) (f := fun t => Real.sqrt 2*transformedKernel a z t)
  F
  (fun n => ((hi n).const_mul (weight n)).1.aestronglyMeasurable)
  (fun n => Filter.Eventually.of_forall (fun t ht => by
   rw [uIoc_of_le hr.le] at ht
   rw [Real.norm_eq_abs, abs_of_nonneg (hpos n t ht.1.le)]))
  (Filter.Eventually.of_forall (fun t ht => by
   rw [uIoc_of_le hr.le] at ht
   exact (hs t ht).summable))
  hiSum
  (Filter.Eventually.of_forall (fun t ht => by
   rw [uIoc_of_le hr.le] at ht
   exact hs t ht))
 simpa only [F, intervalIntegral.integral_const_mul] using hd

theorem transformedTime_hasSum {a z : ℝ} (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 HasSum (fun n => weight n*moment n a z) (2*Real.sqrt 2*transformedTime a z) := by
 have h1 := series_piece ha hz ha ha2 (by linarith)
  (fun n => (moment_integrable n ha hz).1) (transformed_integrable ha ha2 hz hz2).1
 have h2 := series_piece ha hz hz hz2 (by linarith)
  (fun n => (moment_integrable n ha hz).2) (transformed_integrable ha ha2 hz hz2).2
 convert h1.add h2 using 1
 · funext n; unfold moment; ring
 · unfold transformedTime; ring

theorem moment_series_summable {a z : ℝ} (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 Summable (fun n => weight n*moment n a z) :=
 (transformedTime_hasSum ha ha2 hz hz2).summable

theorem transformedTime_series {a z : ℝ} (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 transformedTime a z = (1/(2*Real.sqrt 2))*∑' n, weight n*moment n a z := by
 rw [(transformedTime_hasSum ha ha2 hz hz2).tsum_eq]
 have h : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
 field_simp

end PendulumTimeMap
