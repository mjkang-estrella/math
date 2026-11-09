import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic
set_option autoImplicit false
namespace MathDB358323
open PowerSeries
noncomputable def F (z : ℂ) : PowerSeries ℂ :=
  (((X : PowerSeries ℂ)^2 + X + 1) * (1 - C z * X))⁻¹
noncomputable def P (n : ℕ) (z : ℂ) : ℂ := coeff n (F z)
theorem generating (z : ℂ) :
    ((X^2 + X + 1) * (1 - C z * X)) * F z = (1 : PowerSeries ℂ) := by
  apply PowerSeries.mul_inv_cancel
  simp

theorem zero_identity :
    (X^2 + X + 1) * F 0 = (1 : PowerSeries ℂ) := by
  simpa using generating 0

theorem recur (n : ℕ) : P (n+2) 0 + P (n+1) 0 + P n 0 = 0 := by
  have h := congrArg (coeff (n+2)) zero_identity
  simp only [add_mul, one_mul, map_add] at h
  rw [show (n+2) = n+2 by rfl, coeff_X_pow_mul] at h
  have hx : coeff (n+2) (X * F 0) = P (n+1) 0 := by
    exact coeff_succ_X_mul (n+1) (F 0)
  rw [hx] at h
  simp only [coeff_one, show n+2 ≠ 0 by omega, ite_false] at h
  dsimp [P] at *
  linear_combination h

theorem period (n : ℕ) : P (n+3) 0 = P n 0 := by
  have h := recur n
  have h' := recur (n+1)
  rw [show n+1+2=n+3 by omega, show n+1+1=n+2 by omega] at h'
  linear_combination h' - h

theorem base : P 2 0 = 0 := by
  have h0 := congrArg (coeff 0) zero_identity
  have h1 := congrArg (coeff 1) zero_identity
  simp [add_mul] at h0
  simp [add_mul, pow_two, mul_assoc, coeff_succ_X_mul] at h1
  have h00 : P 0 0 = 1 := by simpa [P] using h0
  have h11 : P 0 0 + P 1 0 = 0 := by simpa [P] using h1
  have h := recur 0
  linear_combination h - h11

theorem recurring (k : ℕ) : P (3*k+2) 0 = 0 := by
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [show 3*(k+1)+2 = (3*k+2)+3 by omega, period]
    exact ih

def Upper (Q : ℕ → ℂ → ℂ) : Set ℂ :=
  {z | ∀ r : ℝ, 0 < r → ∀ N : ℕ, ∃ m > N, ∃ w : ℂ, Q m w = 0 ∧ dist w z < r}
def Lower (Q : ℕ → ℂ → ℂ) : Set ℂ :=
  {z | ∀ r : ℝ, 0 < r → ∃ N : ℕ, ∀ m > N, ∃ w : ℂ, Q m w = 0 ∧ dist w z < r}
def HasZeroSetLimit (Q : ℕ → ℂ → ℂ) (S : Set ℂ) : Prop := Upper Q = S ∧ Lower Q = S

theorem origin_upper : (0 : ℂ) ∈ Upper P := by
  intro r hr N
  exact ⟨3*N+2, by omega, 0, recurring N, by simpa using hr⟩

theorem source_refutation (t : ℂ) (ht : t ≠ 0) :
    ¬ HasZeroSetLimit P {z : ℂ | ‖z‖ = 1 / ‖t‖} := by
  intro h
  have hz := origin_upper
  rw [h.1] at hz
  have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have : (0 : ℝ) = 1 / ‖t‖ := by simpa using hz
  exact (one_div_ne_zero hn) this.symm
end MathDB358323
namespace MathDB358323
noncomputable def t₁ : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩
theorem root_t₁ : t₁^2 + t₁ + 1 = 0 := by
  apply Complex.ext <;> simp [t₁, pow_two, Complex.mul_re, Complex.mul_im]
  all_goals nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
theorem nonzero_t₁ : t₁ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [t₁] at this

theorem root_norm (t : ℂ) (h : t^2+t+1=0) : ‖t‖ = 1 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  have hy : t.im ≠ 0 := by
    intro hz
    rw [hz] at hr
    nlinarith [sq_nonneg (t.re + 1/2)]
  have hx : t.re = -1/2 := by
    have hh : t.im * (2*t.re+1) = 0 := by nlinarith [hi]
    have := (mul_eq_zero.mp hh).resolve_left hy
    linarith
  have hs : Complex.normSq t = 1 := by
    rw [Complex.normSq_apply]
    nlinarith [hr]
  rw [Complex.norm_def, hs]
  norm_num

theorem minimal_root : ∀ t : ℂ, t^2+t+1=0 → ‖t₁‖ ≤ ‖t‖ := by
  intro t ht
  rw [root_norm t ht, root_norm t₁ root_t₁]

/-- The nonzero parameters are a=b=c=1, with discriminant -3. The generating
identity is `generating`; the root selection is certified by `root_t₁` and
`minimal_root`. The set limit is precisely source Definitions 38--41. -/
theorem literal_counterexample :
    (1:ℝ) ≠ 0 ∧ (1:ℝ)^2-4*1*1 ≤ 0 ∧
    t₁^2+t₁+1=0 ∧
    (∀ t : ℂ, t^2+t+1=0 → ‖t₁‖ ≤ ‖t‖) ∧
    ¬ HasZeroSetLimit P {z : ℂ | ‖z‖ = 1/‖t₁‖} := by
  exact ⟨by norm_num, by norm_num, root_t₁, minimal_root,
    source_refutation t₁ nonzero_t₁⟩
end MathDB358323
namespace MathDB358323
open PowerSeries
def Generated (a b c : ℝ) (Q : ℕ → ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ((C (a:ℂ)*X^2 + C (b:ℂ)*X + C (c:ℂ)) * (1-C z*X)) *
    mk (fun n => Q n z) = 1

theorem generated_witness : Generated 1 1 1 P := by
  intro z
  have hmk : mk (fun n => P n z) = F z := by
    ext n
    simp [P]
  simpa only [Complex.ofReal_one, map_one, one_mul, hmk] using generating z

theorem exact_mathdb_negation :
    ¬ (∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → b^2-4*a*c ≤ 0 →
      ∀ Q : ℕ → ℂ → ℂ, Generated a b c Q →
      ∀ t : ℂ, (a:ℂ)*t^2 + (b:ℂ)*t + (c:ℂ) = 0 →
      (∀ s : ℂ, (a:ℂ)*s^2 + (b:ℂ)*s + (c:ℂ) = 0 → ‖t‖ ≤ ‖s‖) →
      HasZeroSetLimit Q {z : ℂ | ‖z‖ = 1/‖t‖}) := by
  intro h
  apply source_refutation t₁ nonzero_t₁
  apply h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    P generated_witness t₁
  · simpa using root_t₁
  · simpa using minimal_root
end MathDB358323
