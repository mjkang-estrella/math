import Mathlib

/-!
Elementary formal checks for an EXCLUDED research lead. These are not a
formalization of Kellner's recurrence or Matsuno's all-variable theorem.
The explicit coefficient formula below is defined, not derived from psi.
-/
namespace AstraAnalysisR2
open Finset

def weight {N : ℕ} (m : Fin N → ℕ) : ℕ := ∑ i, (i.val + 1) * m i

def parts {N : ℕ} (m : Fin N → ℕ) : ℕ := ∑ i, m i

def cycleDenom {N : ℕ} (m : Fin N → ℕ) : ℚ :=
  ∏ i, ((i.val + 1 : ℕ) : ℚ) ^ m i * ((m i).factorial : ℚ)

def proposedCoeff {N : ℕ} (n : ℕ) (m : Fin N → ℕ) : ℚ :=
  (-1 : ℚ) ^ (weight m + 1) * (n.factorial : ℚ) *
    (((n - weight m + parts m - 1).choose (parts m - 1) : ℕ) : ℚ) / cycleDenom m

theorem cycleDenom_pos {N : ℕ} (m : Fin N → ℕ) : 0 < cycleDenom m := by
  unfold cycleDenom
  apply Finset.prod_pos
  intro i hi
  apply mul_pos
  · apply pow_pos
    exact_mod_cast Nat.succ_pos i.val
  · exact_mod_cast Nat.factorial_pos (m i)

theorem proposedCoeff_ne_zero {N : ℕ} (n : ℕ) (m : Fin N → ℕ)
    (hw : weight m ≤ n) (hd : 0 < parts m) : proposedCoeff n m ≠ 0 := by
  have hle : parts m - 1 ≤ n - weight m + parts m - 1 := by omega
  have hc : (0 : ℚ) <
      (((n - weight m + parts m - 1).choose (parts m - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_pos hle
  unfold proposedCoeff
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero _ (by norm_num)
      · exact_mod_cast Nat.factorial_ne_zero n
    · exact ne_of_gt hc
  · exact ne_of_gt (cycleDenom_pos m)

theorem resummation_cancellation {R : Type*} [CommRing R] (t p s e : R)
    (h : p = t * p + s + 1 - e - (t - 1) * p) : e = 1 + s := by
  linear_combination h

/-- Exact degree-four check against the actual source Table 1.1. -/
theorem degree_four_Bell (x₁ x₂ x₃ x₄ : ℚ) :
    (let b₁ := -x₁;
    let b₂ := -2 * (x₁ - x₂ / 2);
    let b₃ := -6 * (x₁ - x₂ / 2 + x₃ / 3);
    let b₄ := -24 * (x₁ - x₂ / 2 + x₃ / 3 - x₄ / 4);
    -(b₁^4 + 6*b₁^2*b₂ + 3*b₂^2 + 4*b₁*b₃ + b₄) =
      24*x₁ - 36*x₁^2 + 12*x₁^3 - x₁^4 - 6*x₁^2*x₂ +
      24*x₁*x₂ - 8*x₁*x₃ - 12*x₂ - 3*x₂^2 + 8*x₃ - 6*x₄) := by
  dsimp
  ring

#check AstraAnalysisR2.cycleDenom_pos
#print axioms AstraAnalysisR2.cycleDenom_pos
#check AstraAnalysisR2.proposedCoeff_ne_zero
#print axioms AstraAnalysisR2.proposedCoeff_ne_zero
#check AstraAnalysisR2.resummation_cancellation
#print axioms AstraAnalysisR2.resummation_cancellation
#check AstraAnalysisR2.degree_four_Bell
#print axioms AstraAnalysisR2.degree_four_Bell
end AstraAnalysisR2
