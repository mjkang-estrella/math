import SuffixUnion
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
namespace LiteralGame
open Filter
open scoped Topology

theorem fib_lower_pair (n : ℕ) :
    (3/2:ℝ)^n / 2 ≤ (F n:ℝ) ∧ (3/2:ℝ)^(n+1) / 2 ≤ (F (n+1):ℝ) := by
  induction n with
  | zero => norm_num [F]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr : (F (n+2):ℝ) = (F n:ℝ) + (F (n+1):ℝ) := by
      exact_mod_cast F_rec n
    rw [show n+1+1=n+2 by omega, hr, pow_add, pow_succ] at *
    norm_num at *
    have hp : 0 ≤ (3/2:ℝ)^n := by positivity
    nlinarith

theorem fib_upper (n : ℕ) : F n ≤ 2^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [F]
  | one => norm_num [F]
  | more n h₁ h₂ =>
    rw [F_rec, pow_succ, pow_succ]
    have hh : 2^n ≤ 2^(n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem eventual_fib_large : ∀ᶠ n : ℕ in atTop,
    (n:ℝ)^20 + n ≤ (F n:ℝ)/(192*(n:ℝ)^3) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^23 / (3/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 23 (by norm_num)
  have he := ht.eventually (gt_mem_nhds (show (0:ℝ)<1/768 by norm_num))
  filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hp : (0:ℝ)<(3/2:ℝ)^n := by positivity
  have hh := (div_lt_iff₀ hp).mp hn
  have hf := (fib_lower_pair n).1
  have hp19 : (1:ℝ) ≤ (n:ℝ)^19 := one_le_pow₀ hx
  have hn20 : (n:ℝ) ≤ (n:ℝ)^20 := by
    calc
      (n:ℝ) = (n:ℝ)*1 := by ring
      _ ≤ (n:ℝ)*(n:ℝ)^19 := mul_le_mul_of_nonneg_left hp19 (by positivity)
      _ = (n:ℝ)^20 := by ring
  apply (le_div_iff₀ (by positivity : (0:ℝ)<192*(n:ℝ)^3)).mpr
  have heq : (n:ℝ)^23 = (n:ℝ)^20*(n:ℝ)^3 := by ring
  rw [heq] at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hn20) (pow_nonneg (by positivity : (0:ℝ)≤n) 3)]

theorem blockLower_real (n : ℕ) : (blockLower n:ℝ) = 1/(8*(n:ℝ)^3) := by
  simp only [blockLower, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  push_cast
  ring

theorem exp_power_bound (x : ℝ) (hx : 0 ≤ 1-x) (k : ℕ) :
    (1-x)^k ≤ Real.exp (-x*(k:ℝ)) := by
  calc
    _ ≤ (Real.exp (-x))^k := pow_le_pow_left₀ hx (by
      have := Real.add_one_le_exp (-x); linarith) k
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem mark_exponential {N n : ℕ} (hn : 1≤n) (hN : 12≤N) :
    (((2:ℚ)^(n^20)*(1-blockLower n/2)^(N/6):ℚ):ℝ) ≤
      Real.exp ((n:ℝ)^20-(N:ℝ)/(192*(n:ℝ)^3)) := by
  have hb := blockLower_bounds hn
  have hb' : (0:ℝ) ≤ 1-(blockLower n:ℝ)/2 := by exact_mod_cast (show (0:ℚ)≤1-blockLower n/2 by linarith)
  have hp := exp_power_bound ((blockLower n:ℝ)/2) hb' (N/6)
  have htwo : (2:ℝ)^(n^20) ≤ Real.exp ((n:ℝ)^20) := by
    have ht : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ht (n^20)
    simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_pow] using this
  have hj : (N:ℝ)/12 ≤ (N/6:ℕ) := by
    have hr := Nat.mod_add_div N 6
    have hm := Nat.mod_lt N (by omega : 0<6)
    have hd : 1 ≤ N/6 := by omega
    have hnat : N ≤ 12*(N/6) := by omega
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<12)).mpr
    exact_mod_cast (show N ≤ (N/6)*12 by omega)
  push_cast
  calc
    _ ≤ Real.exp ((n:ℝ)^20) * Real.exp (-((blockLower n:ℝ)/2)*(N/6:ℕ)) :=
      mul_le_mul htwo hp (by positivity) (by positivity)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [blockLower_real]
      have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have hh := mul_le_mul_of_nonneg_left hj (show (0:ℝ)≤1/(16*(n:ℝ)^3) by positivity)
      ring_nf at hh ⊢
      linarith

end LiteralGame
