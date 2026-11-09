import Growth
set_option autoImplicit false
namespace LiteralGame
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def intervalError (n : ℕ) : ℝ :=
  Real.exp (-(n:ℝ)) + (4/(n:ℝ)^18 + 6/(n:ℝ)^3 + 4/(n:ℝ)^9)

theorem inverse_power_limit (k : ℕ) (hk : 0<k) :
    Tendsto (fun n : ℕ => (n:ℝ)^k) atTop atTop :=
  (tendsto_pow_atTop (ne_of_gt hk)).comp tendsto_natCast_atTop_atTop

theorem intervalError_limit : Tendsto intervalError atTop (𝓝 0) := by
  unfold intervalError
  have he : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hi (k : ℕ) (hk : 0<k) (c : ℝ) :
      Tendsto (fun n : ℕ => c/(n:ℝ)^k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=c)).mul
      (tendsto_inv_atTop_zero.comp (inverse_power_limit k hk))
  simpa only [add_zero] using he.add (((hi 18 (by omega) 4).add
    (hi 3 (by omega) 6)).add (hi 9 (by omega) 4))

theorem concentration_polynomial {n : ℕ} (hn : 2≤n) :
    4/(2*(n:ℝ)^20/(2*(n:ℝ)+1)) +
      2*(3*(n:ℝ)^6+2)/Real.sqrt (2*(n:ℝ)^20/(2*(n:ℝ)+1)) ≤
      4/(n:ℝ)^18 + 6/(n:ℝ)^3 + 4/(n:ℝ)^9 := by
  have hx : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ)<n := by linarith
  have h18 : (0:ℝ)<(n:ℝ)^18 := by positivity
  have h9 : (0:ℝ)<(n:ℝ)^9 := by positivity
  have hl : (n:ℝ)^18 ≤ 2*(n:ℝ)^20/(2*(n:ℝ)+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hsq : 2*(n:ℝ)+1 ≤ 2*(n:ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq (le_of_lt h18)
    nlinarith only [hh, show (n:ℝ)^18*(n:ℝ)^2=(n:ℝ)^20 by ring]
  have hs : (n:ℝ)^9 ≤ Real.sqrt (2*(n:ℝ)^20/(2*(n:ℝ)+1)) := by
    have hh := Real.sqrt_le_sqrt hl
    have he : (n:ℝ)^18 = ((n:ℝ)^9)^2 := by ring
    rwa [he, Real.sqrt_sq (le_of_lt h9)] at hh
  have h₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) h18 hl
  have h₂ := div_le_div_of_nonneg_left (show (0:ℝ)≤2*(3*(n:ℝ)^6+2) by positivity) h9 hs
  have hid : 2*(3*(n:ℝ)^6+2)/(n:ℝ)^9 = 6/(n:ℝ)^3+4/(n:ℝ)^9 := by
    field_simp
    ring
  linarith

theorem index_le_fib (n : ℕ) : n ≤ F n := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => norm_num [F]
  | more n h₁ h₂ =>
    have hp : 0<F n := Nat.fib_pos.mpr (by omega)
    rw [F_rec]
    omega

theorem actual_interval_uniform : ∀ᶠ n : ℕ in atTop,
    ∀ N : ℕ, F n ≤ N → N < F (n+1) → ∀ a : ℤ,
    (∑ w ∈ completeDomain N, (P N w:ℝ) *
      (if a ≤ (w.length:ℤ) ∧ (w.length:ℤ) ≤ a+(3*n^6:ℕ) then 1 else 0)) ≤
      intervalError n := by
  filter_upwards [eventual_fib_large, eventually_ge_atTop 12] with n hg hn
  intro N hlow hhigh a
  have hN : 12≤N := le_trans hn ((index_le_fib n).trans hlow)
  have hm := mark_exponential (by omega : 1≤n) hN
  have hcast : (F n:ℝ) ≤ N := by exact_mod_cast hlow
  have hden : (0:ℝ)<192*(n:ℝ)^3 := by positivity
  have hg' := hg.trans (div_le_div_of_nonneg_right hcast (le_of_lt hden))
  have hex : Real.exp ((n:ℝ)^20-(N:ℝ)/(192*(n:ℝ)^3)) ≤ Real.exp (-(n:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hi := actual_finite_interval_tail (by omega : 1≤n) hhigh (n^20)
    (by positivity) a (3*n^6)
  have hc := concentration_polynomial (by omega : 2≤n)
  push_cast at hi
  push_cast at hm
  push_cast
  dsimp [intervalError]
  linarith

end LiteralGame
