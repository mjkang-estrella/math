import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Filter

namespace MittagModulus

/-- A finite product of the moments of an atom/Beta mixture.
The scale is N=n+1 and there are N+1 factors. -/
noncomputable def momentApprox (β q : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ ((1 - β) * q) *
    ∏ k ∈ Finset.range (n + 2), ((1 + β * q + (k : ℝ)) / (1 + q + (k : ℝ)))

theorem momentApprox_pos {β q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) (n : ℕ) :
    0 < momentApprox β q n := by
  unfold momentApprox
  apply mul_pos (Real.rpow_pos_of_pos (by positivity) _)
  apply Finset.prod_pos
  intro k _
  apply div_pos <;> positivity

theorem momentApprox_eq_gammaSeq_ratio {β q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (n : ℕ) :
    momentApprox β q n =
      Real.GammaSeq (1 + q) (n + 1) / Real.GammaSeq (1 + β * q) (n + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hf : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have ha : (∏ k ∈ Finset.range (n + 2), (1 + q + (k : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    positivity
  have hb : (∏ k ∈ Finset.range (n + 2), (1 + β * q + (k : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    positivity
  have hp : ((n : ℝ) + 1) ^ (1 + β * q) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hn _)
  have he : (1 - β) * q = (1 + q) - (1 + β * q) := by ring
  unfold momentApprox Real.GammaSeq
  push_cast
  rw [he, Real.rpow_sub hn, Finset.prod_div_distrib]
  field_simp

theorem momentApprox_tendsto {β q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    Tendsto (momentApprox β q) atTop
      (nhds (Real.Gamma (1 + q) / Real.Gamma (1 + β * q))) := by
  have ha := (Real.GammaSeq_tendsto_Gamma (1 + q)).comp (tendsto_add_atTop_nat 1)
  have hb := (Real.GammaSeq_tendsto_Gamma (1 + β * q)).comp (tendsto_add_atTop_nat 1)
  have hne : Real.Gamma (1 + β * q) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  exact (ha.div hb hne).congr (fun n => (momentApprox_eq_gammaSeq_ratio hβ hq n).symm)

theorem rpow_successor_lower {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) :
    1 + d / (x + 1) ≤ ((x + 1) / x) ^ d := by
  have hxp : 0 < x + 1 := by positivity
  have hr : 0 < (x + 1) / x := div_pos hxp hx
  have hlog := Real.one_sub_inv_le_log_of_pos hr
  have he : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by
    field_simp
    ring_nf
  rw [he] at hlog
  calc
    1 + d / (x + 1) = 1 + d * (1 / (x + 1)) := by ring
    _ ≤ 1 + d * Real.log ((x + 1) / x) := by gcongr
    _ ≤ Real.exp (Real.log ((x + 1) / x) * d) := by
      nlinarith [Real.add_one_le_exp (Real.log ((x + 1) / x) * d)]
    _ = ((x + 1) / x) ^ d := (Real.rpow_def_of_pos hr _).symm

theorem momentApprox_succ {β q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) (n : ℕ) :
    momentApprox β q (n + 1) = momentApprox β q n *
      ((((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ ((1 - β) * q) *
        (((n : ℝ) + 3 + β * q) / ((n : ℝ) + 3 + q))) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hp : ((n : ℝ) + 1) ^ ((1 - β) * q) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hn _)
  unfold momentApprox
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.prod_range_succ]
  push_cast
  rw [Real.div_rpow (by positivity : 0 ≤ (n : ℝ) + 2) hn.le]
  have hden : (n : ℝ) + 3 + q ≠ 0 := by positivity
  field_simp
  ring_nf

theorem euler_step_ge_one {x β q : ℝ} (hx : 0 < x)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hq : 0 ≤ q) :
    1 ≤ ((x + 1) / x) ^ ((1 - β) * q) *
      ((x + 2 + β * q) / (x + 2 + q)) := by
  have hd : 0 ≤ (1 - β) * q := mul_nonneg (by linarith) hq
  have hn : 0 < x + 2 + β * q := by positivity
  have hden : 0 < x + 2 + q := by positivity
  have hr := rpow_successor_lower hx hd
  have he : (1 + (1 - β) * q / (x + 1)) * (x + 2 + β * q) -
      (x + 2 + q) = (1 - β) * q * (1 + β * q) / (x + 1) := by
    field_simp
    ring_nf
  have hgap : 0 ≤ (1 - β) * q * (1 + β * q) / (x + 1) := by positivity
  have hbase : x + 2 + q ≤
      (1 + (1 - β) * q / (x + 1)) * (x + 2 + β * q) := by linarith
  rw [← mul_div_assoc, le_div_iff₀ hden]
  calc
    1 * (x + 2 + q) = x + 2 + q := by ring
    _ ≤ (1 + (1 - β) * q / (x + 1)) * (x + 2 + β * q) := hbase
    _ ≤ ((x + 1) / x) ^ ((1 - β) * q) * (x + 2 + β * q) :=
      mul_le_mul_of_nonneg_right hr hn.le

theorem momentApprox_monotone {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hq : 0 ≤ q) : Monotone (momentApprox β q) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [momentApprox_succ hβ0 hq]
  have hs := euler_step_ge_one (by positivity : 0 < (n : ℝ) + 1) hβ0 hβ1 hq
  have hs' : 1 ≤ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ ((1 - β) * q) *
      (((n : ℝ) + 3 + β * q) / ((n : ℝ) + 3 + q)) := by
    convert hs using 1; ring_nf
  exact le_mul_of_one_le_right (momentApprox_pos hβ0 hq n).le hs' 

theorem momentApprox_le_gammaRatio {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hq : 0 ≤ q) (n : ℕ) :
    momentApprox β q n ≤ Real.Gamma (1 + q) / Real.Gamma (1 + β * q) := by
  exact (momentApprox_monotone hβ0 hβ1 hq).ge_of_tendsto
    (momentApprox_tendsto hβ0 hq) n

end MittagModulus
