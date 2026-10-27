import Series
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace BesselFejer

lemma norm_tail_le_twice {f : ℕ → ℝ} (N : ℕ)
    (hstep : ∀ n, N ≤ n → ‖f (n+1)‖ ≤ (1/2 : ℝ) * ‖f n‖) :
    ‖∑' n, f (n+N)‖ ≤ 2 * ‖f N‖ := by
  have hbound (n : ℕ) : ‖f (n+N)‖ ≤ ‖f N‖ * (1/2 : ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep (n+N) (by omega)
      have he : n+1+N = n+N+1 := by omega
      rw [he]
      calc
        ‖f (n+N+1)‖ ≤ (1/2 : ℝ)*‖f (n+N)‖ := hh
        _ ≤ (1/2 : ℝ)*(‖f N‖*(1/2 : ℝ)^n) := by gcongr
        _ = ‖f N‖*(1/2 : ℝ)^(n+1) := by ring
  have hg := (hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖ < 1 by norm_num)).mul_left ‖f N‖
  have hb := tsum_of_norm_bounded hg hbound
  norm_num at hb
  simpa [Real.norm_eq_abs, mul_comm] using hb

lemma term_contract (q : ℝ) (hq : |q| ≤ 9) (n : ℕ) (hn : 20 ≤ n) :
    ‖term (n+1) q‖ ≤ (1/2 : ℝ) * ‖term n q‖ := by
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < ((n+1 : ℕ) : ℝ)^2 := by positivity
  have hfac : ‖-(q / ((n+1 : ℕ) : ℝ)^2)‖ ≤ (1/2 : ℝ) := by
    simp only [norm_neg, norm_div, norm_pow, Real.norm_eq_abs]
    rw [abs_of_pos (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity)]
    rw [div_le_iff₀ hp]
    push_cast
    nlinarith
  rw [term_succ, norm_mul]
  exact mul_le_mul_of_nonneg_right hfac (norm_nonneg _)

lemma series_error (q : ℝ) (hq : |q| ≤ 9) :
    |series q - ∑ n ∈ Finset.range 20, term n q| ≤
      2 * (9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 := by
  have hs := (term_summable q).sum_add_tsum_nat_add 20
  have ht := norm_tail_le_twice (f := fun n => term n q) 20 (fun n hn => term_contract q hq n hn)
  have he : series q - ∑ n ∈ Finset.range 20, term n q = ∑' n, term (n+20) q := by
    dsimp [series]
    linarith [hs]
  rw [he, ← Real.norm_eq_abs]
  calc
    ‖∑' n, term (n+20) q‖ ≤ 2 * ‖term 20 q‖ := ht
    _ ≤ 2 * (9 : ℝ)^20 / ((20 : ℕ).factorial : ℝ)^2 := by
      rw [term_norm]
      have hh : |q|^20 ≤ (9 : ℝ)^20 := pow_le_pow_left₀ (abs_nonneg q) hq 20
      have hd : (0 : ℝ) < ((20 : ℕ).factorial : ℝ)^2 := by positivity
      apply (le_div_iff₀ hd).mpr
      field_simp
      nlinarith

lemma hterm_succ (n : ℕ) (q : ℝ) :
    hterm (n+1) q = -(q / (((n+1 : ℕ) : ℝ) * ((n+2 : ℕ) : ℝ))) * hterm n q := by
  simp only [hterm, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp
  ring

lemma hterm_contract (q : ℝ) (hq : |q| ≤ 9) (n : ℕ) (hn : 20 ≤ n) :
    ‖hterm (n+1) q‖ ≤ (1/2 : ℝ) * ‖hterm n q‖ := by
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) * ((n+2 : ℕ) : ℝ) := by positivity
  have hfac : ‖-(q / (((n+1 : ℕ) : ℝ) * ((n+2 : ℕ) : ℝ)))‖ ≤ (1/2 : ℝ) := by
    simp only [norm_neg, norm_div, norm_mul, Real.norm_eq_abs]
    rw [abs_of_pos (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity),
      abs_of_pos (show (0 : ℝ) < ((n+2 : ℕ) : ℝ) by positivity)]
    rw [div_le_iff₀ hp]
    push_cast
    nlinarith
  rw [hterm_succ, norm_mul]
  exact mul_le_mul_of_nonneg_right hfac (norm_nonneg _)

lemma normalizedDerivative_error (q : ℝ) (hq : |q| ≤ 9) :
    |normalizedDerivative q - ∑ n ∈ Finset.range 20, hterm n q| ≤
      2 * (9 : ℝ)^20 / (((20 : ℕ).factorial : ℝ) * ((21 : ℕ).factorial : ℝ)) := by
  have hs := (hterm_summable q).sum_add_tsum_nat_add 20
  have ht := norm_tail_le_twice (f := fun n => hterm n q) 20 (fun n hn => hterm_contract q hq n hn)
  have he : normalizedDerivative q - ∑ n ∈ Finset.range 20, hterm n q =
      ∑' n, hterm (n+20) q := by
    dsimp [normalizedDerivative]
    linarith [hs]
  rw [he, ← Real.norm_eq_abs]
  calc
    ‖∑' n, hterm (n+20) q‖ ≤ 2 * ‖hterm 20 q‖ := ht
    _ ≤ 2 * (9 : ℝ)^20 / (((20 : ℕ).factorial : ℝ) * ((21 : ℕ).factorial : ℝ)) := by
      rw [hterm_norm]
      have hh : |q|^20 ≤ (9 : ℝ)^20 := pow_le_pow_left₀ (abs_nonneg q) hq 20
      have hd : (0 : ℝ) < ((20 : ℕ).factorial : ℝ) * ((21 : ℕ).factorial : ℝ) := by positivity
      apply (le_div_iff₀ hd).mpr
      field_simp
      nlinarith

end BesselFejer
