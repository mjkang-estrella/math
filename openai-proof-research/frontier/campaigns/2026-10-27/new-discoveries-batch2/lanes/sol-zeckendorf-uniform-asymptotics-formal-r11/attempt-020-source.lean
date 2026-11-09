import Uniform
set_option autoImplicit false
namespace LiteralGame
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def suffixError (n : ℕ) : ℝ := Real.exp (-(n:ℝ))
noncomputable def actualSuffixMass (N n : ℕ) : ℝ :=
  ∑ w ∈ completeDomain N, (P N w:ℝ) *
    (if n^6 < w.length-lastSplit w then 1 else 0)

theorem suffixError_limit : Tendsto suffixError atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

theorem suffix_cutoff {n : ℕ} (hn : 8≤n) : 3*n^5+n+3 ≤ n^6 := by
  have hpow : n ≤ n^5 := by
    calc
      n = n*1 := by omega
      _ ≤ n*n^4 := Nat.mul_le_mul_left n (Nat.one_le_pow 4 n (by omega))
      _ = n^5 := by ring
  have hh : 8*n^5 ≤ n*n^5 := Nat.mul_le_mul_right (n^5) hn
  have he : n*n^5 = n^6 := by ring
  omega

theorem literal_suffix_inclusion {n : ℕ} (hn : 8≤n) (w : List Move)
    (hw : n^6 < w.length-lastSplit w) :
    3*n^5+n+3 < w.length-lastSplit w := lt_of_le_of_lt (suffix_cutoff hn) hw

theorem suffix_mass_comparison {n N : ℕ} (hn : 8≤n) :
    actualSuffixMass N n ≤ (suffixTailMass N n (n^5):ℝ) := by
  unfold actualSuffixMass suffixTailMass suffixTailDomain
  rw [Rat.cast_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro w _
  by_cases ht : n^6 < w.length-lastSplit w
  · simp only [ht, ite_true, mul_one, literal_suffix_inclusion hn w ht]
    exact le_refl _
  · simp only [ht, ite_false, mul_zero]
    split_ifs
    · exact Rat.cast_nonneg.mpr (P_nonneg N w)
    · exact le_refl 0

theorem suffix_exponential {n N : ℕ} (hn : 1≤n) (hN : N<F (n+1)) :
    (suffixTailMass N n (n^5):ℝ) ≤ (3*(N:ℝ)+1)*Real.exp (-(n:ℝ)^2/8) := by
  have hb := (Rat.cast_le (K:=ℝ)).mpr (suffixTailMass_bound hn hN (n^5))
  have hlow := blockLower_bounds hn
  have hz : (0:ℝ) ≤ 1-(blockLower n:ℝ) := by exact_mod_cast (sub_nonneg.mpr hlow.2)
  have he := exp_power_bound (blockLower n:ℝ) hz (n^5)
  have hx : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hid : -(blockLower n:ℝ)*(n^5:ℕ) = -(n:ℝ)^2/8 := by
    rw [blockLower_real]
    push_cast
    field_simp
  rw [hid] at he
  push_cast at hb
  exact hb.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem suffix_prefactor {n N : ℕ} (hN : N<F (n+1)) :
    3*(N:ℝ)+1 ≤ Real.exp ((n:ℝ)+3) := by
  have hu : N ≤ 2^(n+1) := (Nat.le_of_lt hN).trans (fib_upper (n+1))
  have he : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) he (n+1)
  rw [← Real.exp_nat_mul] at hp
  have hfour : (4:ℝ) ≤ Real.exp 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) he 2
    norm_num [← Real.exp_nat_mul] at hh
    exact hh
  have hreal : (N:ℝ) ≤ (2:ℝ)^(n+1) := by exact_mod_cast hu
  have hone : (1:ℝ) ≤ (2:ℝ)^(n+1) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ 4*(2:ℝ)^(n+1) := by linarith
    _ ≤ Real.exp 2 * Real.exp ((n:ℝ)+1) := by
      apply mul_le_mul hfour _ (by positivity) (by positivity)
      simpa using hp
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem actual_suffix_uniform : ∀ᶠ n : ℕ in atTop,
    ∀ N : ℕ, F n ≤ N → N < F (n+1) → actualSuffixMass N n ≤ suffixError n := by
  filter_upwards [eventually_ge_atTop 32] with n hn
  intro N _ hN
  have hx : (32:ℝ)≤n := by exact_mod_cast hn
  have h₁ := suffix_mass_comparison (N:=N) (by omega : 8≤n)
  have h₂ := suffix_exponential (by omega : 1≤n) hN
  have h₃ := mul_le_mul_of_nonneg_right (suffix_prefactor hN)
    (le_of_lt (Real.exp_pos (-(n:ℝ)^2/8)))
  rw [← Real.exp_add] at h₃
  have h₄ : Real.exp ((n:ℝ)+3+(-(n:ℝ)^2/8)) ≤ suffixError n := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end LiteralGame
