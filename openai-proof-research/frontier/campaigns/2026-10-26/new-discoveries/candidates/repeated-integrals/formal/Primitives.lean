import MomentDefs
import JetIntegral

open Set Filter
open scoped ContDiff Topology

namespace RepeatedIntegrals

noncomputable section

def zeroPrimitive (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, ρ t

theorem zeroPrimitive_deriv {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    deriv (zeroPrimitive ρ) = ρ := by
  funext x
  exact Continuous.deriv_integral ρ hρ 0 x

theorem zeroPrimitive_smooth {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (zeroPrimitive ρ) := by
  have hd : Differentiable ℝ (zeroPrimitive ρ) :=
    fun x => (hρ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  apply contDiff_infty.mpr
  intro k
  cases k with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ k =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiff_succ_iff_deriv]
    refine ⟨hd, ?_, ?_⟩
    · intro h
      simp at h
    · rw [zeroPrimitive_deriv hρ.continuous]
      exact hρ.of_le (by simp)

def repeatedPrimitive : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, ρ => ρ
  | k + 1, ρ => zeroPrimitive (repeatedPrimitive k ρ)

theorem repeatedPrimitive_smooth (k : ℕ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (repeatedPrimitive k ρ) := by
  induction k with
  | zero => exact hρ
  | succ k ih => exact zeroPrimitive_smooth ih

theorem repeatedPrimitive_deriv (k : ℕ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    deriv (repeatedPrimitive (k + 1) ρ) = repeatedPrimitive k ρ :=
  zeroPrimitive_deriv (repeatedPrimitive_smooth k hρ).continuous

theorem repeatedPrimitive_iterated (j k : ℕ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    iteratedDeriv j (repeatedPrimitive (j + k) ρ) = repeatedPrimitive k ρ := by
  induction j with
  | zero => simp only [Nat.zero_add, iteratedDeriv_zero]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega, iteratedDeriv_succ',
      repeatedPrimitive_deriv (j + k) hρ]
    exact ih

theorem repeatedPrimitive_zero (k : ℕ) (ρ : ℝ → ℝ) :
    repeatedPrimitive (k + 1) ρ 0 = 0 := by
  simp [repeatedPrimitive, zeroPrimitive]

theorem iterated_deriv_compose (i j : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i + j) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem repeatedPrimitive_initial (n j : ℕ) (hj : j ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) :
    iteratedDeriv j (repeatedPrimitive (n + 1) ρ) 0 = 0 := by
  rw [show n + 1 = j + (n - j + 1) by omega, repeatedPrimitive_iterated j _ hρ]
  exact repeatedPrimitive_zero _ _

theorem goodDensity_higher_endpoint {ρ : ℝ → ℝ} (hρ : GoodDensity ρ) (k : ℕ)
    (hk : 0 < k) : iteratedDeriv k ρ 0 = 0 ∧ iteratedDeriv k ρ 1 = 0 := by
  constructor
  · rw [hρ.2.2.1.iteratedDeriv_eq k]
    simp [iteratedDeriv_const, hk.ne']
  · rw [hρ.2.2.2.iteratedDeriv_eq k]
    simp [iteratedDeriv_const, hk.ne']

theorem repeatedPrimitive_higher_endpoint (n j : ℕ) (hj : n + 1 < j)
    {ρ : ℝ → ℝ} (hρ : GoodDensity ρ) :
    iteratedDeriv j (repeatedPrimitive (n + 1) ρ) 0 = 0 ∧
      iteratedDeriv j (repeatedPrimitive (n + 1) ρ) 1 = 0 := by
  have hi : iteratedDeriv (n + 1) (repeatedPrimitive (n + 1) ρ) = ρ := by
    simpa only [Nat.add_zero, repeatedPrimitive] using
      repeatedPrimitive_iterated (n + 1) 0 hρ.1
  rw [show j = (j - (n + 1)) + (n + 1) by omega,
    ← iterated_deriv_compose, hi]
  exact goodDensity_higher_endpoint hρ _ (by omega)

end

end RepeatedIntegrals
