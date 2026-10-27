import Mathlib
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators
open Filter Set
namespace BesselFejer

def term (n : ℕ) (q : ℝ) : ℝ := (-1 : ℝ)^n * q^n / (n.factorial : ℝ)^2

def hterm (n : ℕ) (q : ℝ) : ℝ :=
  (-1 : ℝ)^n * q^n / ((n.factorial : ℝ) * ((n+1).factorial : ℝ))

def series (q : ℝ) : ℝ := ∑' n, term n q

def normalizedDerivative (q : ℝ) : ℝ := ∑' n, hterm n q

def besselJ0 (x : ℝ) : ℝ := series (x^2/4)

def nextZero (a : ℝ) : ℝ := sInf {x : ℝ | a < x ∧ besselJ0 x = 0}

def sourceZero : ℕ → ℝ
  | 0 => 0
  | n+1 => nextZero (sourceZero n)

def sourceKernel (α : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  if M = 0 then 1 else ∑ m ∈ Finset.range M,
    (1 - ((m+1 : ℕ) : ℝ) / ((M+1 : ℕ) : ℝ)) *
      (sourceZero (m+1))^α * besselJ0 (sourceZero (m+1) * x)

def SourceClaim365454 : Prop :=
  ∀ (α : ℝ), 0 ≤ α → α ≤ 1/2 → ∀ (M : ℕ), 0 < M →
    ∀ (x : ℝ), 0 ≤ x → x ≤ 1 → 0 ≤ sourceKernel α M x

lemma term_norm (n : ℕ) (q : ℝ) :
    ‖term n q‖ = |q|^n / (n.factorial : ℝ)^2 := by
  simp [term, norm_div, norm_mul, norm_pow, Real.norm_eq_abs]

lemma hterm_norm (n : ℕ) (q : ℝ) :
    ‖hterm n q‖ = |q|^n / ((n.factorial : ℝ) * ((n+1).factorial : ℝ)) := by
  simp [hterm, norm_div, norm_mul, norm_pow, Real.norm_eq_abs]

lemma term_norm_le (n : ℕ) (q : ℝ) :
    ‖term n q‖ ≤ |q|^n / (n.factorial : ℝ) := by
  rw [term_norm]
  have h : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

lemma hterm_norm_le (n : ℕ) (q : ℝ) :
    ‖hterm n q‖ ≤ |q|^n / (n.factorial : ℝ) := by
  rw [hterm_norm]
  have h : (1 : ℝ) ≤ (n+1).factorial := by exact_mod_cast Nat.factorial_pos (n+1)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [show (0 : ℝ) < n.factorial by positivity]

lemma term_summable (q : ℝ) : Summable (fun n => term n q) :=
  (Real.summable_pow_div_factorial |q|).of_norm_bounded (fun n => term_norm_le n q)

lemma hterm_summable (q : ℝ) : Summable (fun n => hterm n q) :=
  (Real.summable_pow_div_factorial |q|).of_norm_bounded (fun n => hterm_norm_le n q)

lemma term_succ (n : ℕ) (q : ℝ) :
    term (n+1) q = -(q / ((n+1 : ℕ) : ℝ)^2) * term n q := by
  simp only [term, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp

lemma term_succ_hasDerivAt (n : ℕ) (q : ℝ) :
    HasDerivAt (term (n+1)) (-hterm n q) q := by
  change HasDerivAt (fun x : ℝ => (-1 : ℝ)^(n+1) * x^(n+1) /
    (((n+1).factorial : ℝ)^2)) _ q
  convert (((hasDerivAt_id q).pow (n+1)).const_mul ((-1 : ℝ)^(n+1))).div_const
    (((n+1).factorial : ℝ)^2) using 1
  all_goals simp [hterm, Nat.factorial_succ, pow_succ]
  all_goals field_simp

lemma series_eq_shift (q : ℝ) : series q = 1 + ∑' n, term (n+1) q := by
  simpa [series, term] using ((term_summable q).sum_add_tsum_nat_add 1).symm

lemma series_zero : series 0 = 1 := by
  rw [series_eq_shift]
  simp [term]

lemma series_hasDerivAt (q : ℝ) :
    HasDerivAt series (-normalizedDerivative q) q := by
  let R : ℝ := |q| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hq : q ∈ Ioo (-R) R := by
    constructor <;> dsimp [R] <;> linarith [le_abs_self q, neg_abs_le q]
  have h0 : (0 : ℝ) ∈ Ioo (-R) R := by constructor <;> linarith
  have hsum0 : Summable (fun n => term (n+1) (0 : ℝ)) :=
    (summable_nat_add_iff 1).mpr (term_summable 0)
  have hd := hasDerivAt_tsum_of_isPreconnected
    (u := fun n => R^n / (n.factorial : ℝ))
    (g := fun n z => term (n+1) z) (g' := fun n z => -hterm n z)
    (Real.summable_pow_div_factorial R) isOpen_Ioo
    (convex_Ioo (-R) R).isPreconnected
    (fun n z _ => term_succ_hasDerivAt n z) (fun n z hz => by
      rw [norm_neg]
      calc
        ‖hterm n z‖ ≤ |z|^n / (n.factorial : ℝ) := hterm_norm_le n z
        _ ≤ R^n / (n.factorial : ℝ) := by
          have hzR : |z| ≤ R := (abs_le).mpr ⟨le_of_lt hz.1, le_of_lt hz.2⟩
          gcongr)
    h0 hsum0 hq
  convert hd.const_add 1 using 1
  · exact funext series_eq_shift
  · exact (tsum_neg (f := fun n => hterm n q)).symm

lemma besselJ0_hasDerivAt (x : ℝ) :
    HasDerivAt besselJ0 (-(x/2) * normalizedDerivative (x^2/4)) x := by
  convert (series_hasDerivAt (x^2/4)).comp x
    (((hasDerivAt_id x).pow 2).div_const 4) using 1
  · rfl
  · simp
    ring

lemma besselJ0_continuous : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr (fun x => (besselJ0_hasDerivAt x).continuousAt)

lemma besselJ0_zero : besselJ0 0 = 1 := by
  simpa [besselJ0] using series_zero

end BesselFejer
