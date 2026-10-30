module
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
 <;> ring

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
 | zero => simp [weight, Ring.choose_zero_right]
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
  simpa only [Real.dist_eq, sub_zero, abs_div, abs_neg, abs_ofNat] using (div_lt_one (by norm_num : (0:ℝ)<2)).mpr ht
 have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1/2:ℝ))).hasSum hmem
 simpa only [binomialSeries_apply, List.prod_ofFn_const, smul_eq_mul, zero_add,
  ← mul_pow, weight_eq_choose, mul_assoc, show (-1/2:ℝ)*t=-t/2 by ring,
  show (1+ -t/2:ℝ)=1-t/2 by ring] using h

end PendulumTimeMap
