import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
set_option warningAsError true
open Finset Filter
open scoped Topology
namespace JacobiShifted
/-- The literal finite rational sum in primary Theorem 1.4. -/
def binomialOddSum (m : ℕ) : ℚ :=
  ∑ j ∈ range (m + 1), (m.choose j : ℚ) / (2 * j + 1)
/-- The odd double factorial, as a finite product. -/
def oddProduct (n : ℕ) : ℕ := ∏ j ∈ range (n + 1), (2 * j + 1)
/-- Primary Section 3's coefficient `c_n`. -/
def momentCoeff (n : ℕ) : ℚ := (n.factorial : ℚ) / oddProduct n
lemma oddProduct_pos (n : ℕ) : 0 < oddProduct n := by
  exact prod_pos (fun j _ => by omega)
lemma oddProduct_succ (n : ℕ) : oddProduct (n + 1) = oddProduct n * (2 * n + 3) := by
  unfold oddProduct
  rw [prod_range_succ]
  congr 1
lemma momentCoeff_zero : momentCoeff 0 = 1 := by norm_num [momentCoeff, oddProduct]
lemma momentCoeff_succ (n : ℕ) :
    (2 * (n : ℚ) + 3) * momentCoeff (n + 1) = (n + 1) * momentCoeff n := by
  rw [momentCoeff, momentCoeff, Nat.factorial_succ, oddProduct_succ]
  push_cast
  have h : (oddProduct n : ℚ) ≠ 0 := by exact_mod_cast (oddProduct_pos n).ne'
  field_simp
lemma binomialOddSum_pos (m : ℕ) : 0 < binomialOddSum m := by
  unfold binomialOddSum
  apply sum_pos' (fun j _ => div_nonneg (by positivity) (by positivity))
  exact ⟨0, by simp, by simp⟩
lemma binomialOddSum_ne_zero (m : ℕ) : binomialOddSum m ≠ 0 :=
  (binomialOddSum_pos m).ne'
lemma norm_odd (n : ℕ) : ‖(2 * n + 1 : ℚ_[2])‖ = 1 := by
  have hc : (2 * n + 1 : ℚ_[2]) = ((2 * n + 1 : ℕ) : ℚ_[2]) := by push_cast; rfl
  rw [hc]
  apply (Padic.norm_natCast_eq_one_iff).2
  exact Nat.prime_two.coprime_iff_not_dvd.2 (by omega)
lemma norm_oddProduct (n : ℕ) : ‖(oddProduct n : ℚ_[2])‖ = 1 := by
  unfold oddProduct
  push_cast
  rw [norm_prod]
  exact prod_eq_one (fun j _ => by simpa using norm_odd j)
lemma norm_momentCoeff (n : ℕ) :
    ‖(momentCoeff n : ℚ_[2])‖ = ‖(n.factorial : ℚ_[2])‖ := by
  simp only [momentCoeff, Rat.cast_div, Rat.cast_natCast, norm_div, norm_oddProduct, div_one]
lemma norm_nat_le_one (n : ℕ) : ‖(n : ℚ_[2])‖ ≤ 1 := by
  exact_mod_cast Padic.norm_int_le_one (p := 2) (n : ℤ)
lemma norm_momentCoeff_le_one (n : ℕ) : ‖(momentCoeff n : ℚ_[2])‖ ≤ 1 := by
  rw [norm_momentCoeff]
  exact norm_nat_le_one _
lemma norm_momentCoeff_le_factorial {j k : ℕ} (hjk : j ≤ k) :
    ‖(momentCoeff k : ℚ_[2])‖ ≤ ‖(j.factorial : ℚ_[2])‖ := by
  rw [norm_momentCoeff]
  obtain ⟨a, ha⟩ := Nat.factorial_dvd_factorial hjk
  rw [ha, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_nat_le_one a)
lemma factorial_norm_le (n : ℕ) :
    ‖(n.factorial : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ (n / 2) := by
  have hv : n / 2 ≤ padicValNat 2 n.factorial := by
    have h := padicValNat_factorial_mul (p := 2) (n / 2)
    rw [padicValNat_mul_div_factorial] at h
    omega
  have hd : (2 : ℤ) ^ (n / 2) ∣ (n.factorial : ℤ) := by
    exact_mod_cast (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero n)).2 hv
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 2) (n.factorial : ℤ) (n / 2)).2 hd
  simpa only [Int.cast_natCast, Nat.cast_ofNat, zpow_neg, zpow_natCast, one_div, inv_pow] using h
lemma momentCoeff_tendsto : Tendsto (fun n => (momentCoeff n : ℚ_[2])) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => (norm_momentCoeff n).le.trans (factorial_norm_le n))
  have ht : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    exact tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2 * b, fun n hn => by omega⟩)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp ht
lemma bounded_mul_summable (f : ℕ → ℚ_[2]) (hf : ∀ n, ‖f n‖ ≤ 1) :
    Summable (fun n => (momentCoeff n : ℚ_[2]) * f n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => (norm_mul _ _).le.trans (mul_le_of_le_one_right (norm_nonneg _) (hf n)))
  exact (tendsto_zero_iff_norm_tendsto_zero).1 momentCoeff_tendsto
/-- All binomial moments, including the zero terms below the lower index. -/
def binomialMoment (i : ℕ) : ℚ_[2] :=
  ∑' k : ℕ, (momentCoeff k : ℚ_[2]) * (k.choose i : ℚ_[2])
lemma moment_summable (i : ℕ) :
    Summable (fun k => (momentCoeff k : ℚ_[2]) * (k.choose i : ℚ_[2])) :=
  bounded_mul_summable _ (fun _ => norm_nat_le_one _)
lemma norm_binomialMoment_le_one (i : ℕ) : ‖binomialMoment i‖ ≤ 1 := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_nat_le_one _)).trans
    (norm_momentCoeff_le_one k)

lemma choose_moment_identity (k i : ℕ) :
    ((i + 2 : ℕ) : ℚ_[2]) * (k.choose (i + 2) : ℚ_[2]) -
      ((i + 1 : ℕ) : ℚ_[2]) * (k.choose i : ℚ_[2]) =
    (2 * k + 1 : ℚ_[2]) * (k.choose (i + 1) : ℚ_[2]) -
      (k + 1 : ℚ_[2]) * ((k + 1).choose (i + 1) : ℚ_[2]) := by
  have h0 := congrArg (fun n : ℕ => (n : ℚ_[2])) (Nat.add_one_mul_choose_eq k i)
  have h1 := congrArg (fun n : ℕ => (n : ℚ_[2])) (Nat.add_one_mul_choose_eq k (i + 1))
  simp only [Nat.choose_succ_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h0 h1 ⊢
  linear_combination h0 - h1

lemma weighted_summable (f : ℕ → ℕ) :
    Summable (fun k => (momentCoeff k : ℚ_[2]) * (f k : ℚ_[2])) :=
  bounded_mul_summable _ (fun k => norm_nat_le_one (f k))

/-- The positive-index moment recurrence, with its boundary proved explicitly. -/
lemma binomialMoment_recurrence (i : ℕ) :
    (i + 2 : ℚ_[2]) * binomialMoment (i + 2) =
      (i + 1 : ℚ_[2]) * binomialMoment i := by
  let L : ℕ → ℚ_[2] := fun k => (momentCoeff k : ℚ_[2]) *
    (2 * k + 1) * (k.choose (i + 1) : ℚ_[2])
  let R : ℕ → ℚ_[2] := fun k => (momentCoeff k : ℚ_[2]) *
    (k + 1) * ((k + 1).choose (i + 1) : ℚ_[2])
  have hL : Summable L := by
    convert weighted_summable (fun k => (2 * k + 1) * k.choose (i + 1)) using 1
    simp only [L, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_assoc]
  have hR : Summable R := by
    convert weighted_summable (fun k => (k + 1) * (k + 1).choose (i + 1)) using 1
    simp only [R, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc]
  have hshift : ∀ k, L (k + 1) = R k := by
    intro k
    have hc := congrArg (fun q : ℚ => (q : ℚ_[2])) (momentCoeff_succ k)
    push_cast at hc
    dsimp [L, R]
    push_cast
    rw [show (2 * ((k : ℚ_[2]) + 1) + 1) = 2 * k + 3 by ring]
    linear_combination hc * ((k + 1).choose (i + 1) : ℚ_[2])
  have hsum : (∑' k, L k) = ∑' k, R k := by
    have h := hL.sum_add_tsum_nat_add 1
    simpa only [sum_range_one, L, Nat.choose_zero_succ, Nat.cast_zero, mul_zero,
      zero_add, hshift] using h.symm
  have hid : (fun k => (i + 2 : ℚ_[2]) *
      ((momentCoeff k : ℚ_[2]) * (k.choose (i + 2) : ℚ_[2])) -
      (i + 1 : ℚ_[2]) * ((momentCoeff k : ℚ_[2]) * (k.choose i : ℚ_[2]))) =
      (fun k => L k - R k) := by
    funext k
    have h := choose_moment_identity k i
    push_cast at h
    dsimp [L, R]
    linear_combination (momentCoeff k : ℚ_[2]) * h
  have hs := congrArg (fun f : ℕ → ℚ_[2] => ∑' k, f k) hid
  rw [Summable.tsum_sub ((moment_summable (i + 2)).mul_left _) ((moment_summable i).mul_left _),
    tsum_mul_left, tsum_mul_left, Summable.tsum_sub hL hR, hsum, sub_self] at hs
  exact sub_eq_zero.mp hs


lemma moment_even_product (j : ℕ) :
    (∏ t ∈ range j, (2 * t + 1 : ℚ_[2])) * binomialMoment 0 =
      (2 : ℚ_[2]) ^ j * (j.factorial : ℚ_[2]) * binomialMoment (2 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := binomialMoment_recurrence (2 * j)
    push_cast at h ⊢
    rw [prod_range_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show (2 * (j + 1)) = 2 * j + 2 by omega]
    linear_combination (2 * (j : ℚ_[2]) + 1) * ih -
      (2 : ℚ_[2]) ^ j * (j.factorial : ℚ_[2]) * h

/-- Primary Theorem 3.5, proved from convergent moments rather than assumed. -/
lemma moment_zero : binomialMoment 0 = 0 := by
  have hb (j : ℕ) : ‖binomialMoment 0‖ ≤ (1 / 2 : ℝ) ^ j := by
    have h := congrArg norm (moment_even_product j)
    have ho : ‖∏ t ∈ range j, (2 * t + 1 : ℚ_[2])‖ = 1 := by
      rw [norm_prod]
      exact prod_eq_one (fun t _ => norm_odd t)
    rw [norm_mul, ho, one_mul, norm_mul, norm_mul, norm_pow,
      show ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) by simpa using (Padic.norm_p (p := 2))] at h
    rw [h]
    exact (mul_le_of_le_one_right (by positivity) (norm_binomialMoment_le_one _)).trans
      (mul_le_of_le_one_right (by positivity) (norm_nat_le_one _))
  have hzero : ‖binomialMoment 0‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)) hb
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))


lemma coeff_summable : Summable (fun k => (momentCoeff k : ℚ_[2])) := by
  simpa only [Nat.choose_zero_right, Nat.cast_one, mul_one] using moment_summable 0

/-- The convergent tail from source Lemma 3.3. -/
def coeffTail (j : ℕ) : ℚ_[2] := ∑' k : ℕ, (momentCoeff (k + j) : ℚ_[2])

lemma tail_summable (j : ℕ) : Summable (fun k => (momentCoeff (k + j) : ℚ_[2])) :=
  (summable_nat_add_iff j).2 coeff_summable

lemma norm_coeffTail (j : ℕ) : ‖coeffTail j‖ ≤ ‖(j.factorial : ℚ_[2])‖ := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  exact norm_momentCoeff_le_factorial (by omega)

lemma coeffTail_zero : coeffTail 0 = 0 := by
  simpa [coeffTail, binomialMoment] using moment_zero

lemma coeffTail_step (j : ℕ) : coeffTail j = (momentCoeff j : ℚ_[2]) + coeffTail (j + 1) := by
  have h := (tail_summable j).sum_add_tsum_nat_add 1
  simpa [coeffTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

lemma coeffTail_one : coeffTail 1 = -1 := by
  have h := coeffTail_step 0
  rw [coeffTail_zero, momentCoeff_zero, Rat.cast_one] at h
  linear_combination -h

lemma coeffTail_two : coeffTail 2 = -(4 / 3 : ℚ_[2]) := by
  have h := coeffTail_step 1
  have hc : momentCoeff 1 = (1 / 3 : ℚ) := by norm_num [momentCoeff, oddProduct, prod_range_succ]
  rw [coeffTail_one, hc] at h
  push_cast at h
  linear_combination -h

lemma norm_coeffTail_div_succ (j : ℕ) :
    ‖coeffTail (j + 1) / (j + 1 : ℚ_[2])‖ ≤ ‖(j.factorial : ℚ_[2])‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.2 (by exact_mod_cast Nat.succ_ne_zero j))).2
  have h := norm_coeffTail (j + 1)
  rw [Nat.factorial_succ, Nat.cast_mul, norm_mul] at h
  simpa [mul_comm] using h

lemma norm_coeffTail_div_small {j : ℕ} (hj : 2 ≤ j) :
    ‖coeffTail j / (j : ℚ_[2])‖ ≤ 1 / 2 := by
  have htwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by simpa using (Padic.norm_p (p := 2))
  by_cases heq : j = 2
  · subst j
    rw [coeffTail_two]
    have hthree : ‖(3 : ℚ_[2])‖ = 1 := by convert norm_odd 1 using 1; norm_num
    have hfour : ‖(4 : ℚ_[2])‖ = (1 / 2 : ℝ) ^ 2 := by
      calc
        _ = ‖(2 : ℚ_[2]) ^ 2‖ := by norm_num
        _ = _ := by rw [norm_pow, htwo]
    norm_num [norm_div, norm_neg, htwo, hthree, hfour]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    push_cast
    apply (norm_coeffTail_div_succ k).trans
    have h := norm_momentCoeff_le_factorial (j := 2) (k := k) (by omega)
    rw [norm_momentCoeff] at h
    simpa only [show (2 : ℕ).factorial = 2 by rfl, Nat.cast_ofNat, htwo] using h

end JacobiShifted
