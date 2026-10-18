import Mathlib.Tactic

/-!
Copyright (c) 2026 Myeongjin Kang. Released under the MIT license.

Scoped algebra for T027O. This file does not formalize surface topology,
arithmetic orbit density, or the full theorem. The principal-minor derivative
hypotheses below are explicit scalar polynomial identities.
-/

namespace T027O

variable {K : Type*} [Field K] {ι : Type*}

theorem triangle_coboundary (o : ι) (x : ι → ι → K)
    (hdiag : ∀ i, x i i = 0)
    (hpair : ∀ i j, i ≠ j → x i j + x j i = 0)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      x i j + x j k + x k i = 0) :
    ∃ h : ι → K, ∀ i j, x i j = h i - h j := by
  refine ⟨fun i => x i o, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  by_cases hio : i = o
  · subst i
    have hp := hpair o j hij
    change x o j = x o o - x j o
    rw [hdiag]
    linear_combination hp
  by_cases hjo : j = o
  · subst j
    simp [hdiag]
  have ht := htri i j o hij hjo (Ne.symm hio)
  have hp := hpair o i (Ne.symm hio)
  linear_combination ht - hp

/-- The scalar derivative of the sum of the two oriented three-cycles. -/
def cycleDerivative (M E : ι → ι → K) (i j k : ι) : K :=
    E i j * M j k * M k i + M i j * E j k * M k i +
    M i j * M j k * E k i + E i k * M k j * M j i +
    M i k * E k j * M j i + M i k * M k j * E j i

theorem principal_minor_rigidity (o : ι) (M E : ι → ι → K)
    (hnz : ∀ i j, i ≠ j → M i j ≠ 0)
    (hdiag : ∀ i, E i i = 0)
    (hpair : ∀ i j, i ≠ j → E i j * M j i + M i j * E j i = 0)
    (htri : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      cycleDerivative M E i j k = 0)
    (hgeneric : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      M i j * M j k * M k i - M i k * M k j * M j i ≠ 0) :
    ∃ h : ι → K, ∀ i j, E i j = (h i - h j) * M i j := by
  classical
  let x : ι → ι → K := fun i j => if i = j then 0 else E i j / M i j
  have xd : ∀ i, x i i = 0 := by intro i; simp [x]
  have xe : ∀ i j, E i j = x i j * M i j := by
    intro i j
    by_cases hij : i = j
    · subst j; simp [x, hdiag]
    · simp [x, hij, hnz i j hij]
  have xp : ∀ i j, i ≠ j → x i j + x j i = 0 := by
    intro i j hij
    dsimp [x]
    simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
    have hp := hpair i j hij
    field_simp [hnz i j hij, hnz j i (Ne.symm hij)]
    linear_combination hp
  have xt : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
      x i j + x j k + x k i = 0 := by
    intro i j k hij hjk hki
    have hji : x j i = -x i j := by linear_combination xp i j hij
    have hkj : x k j = -x j k := by linear_combination xp j k hjk
    have hik : x i k = -x k i := by linear_combination xp k i hki
    have ht := htri i j k hij hjk hki
    dsimp [cycleDerivative] at ht
    rw [xe i j, xe j k, xe k i, xe i k, xe k j, xe j i,
      hik, hkj, hji] at ht
    have factor :
        (M i j * M j k * M k i - M i k * M k j * M j i) *
          (x i j + x j k + x k i) = 0 := by
      linear_combination ht
    exact (mul_eq_zero.mp factor).resolve_left (hgeneric i j k hij hjk hki)
  obtain ⟨h, hh⟩ := triangle_coboundary o x xd xp xt
  exact ⟨h, fun i j => by rw [xe i j, hh i j]⟩

end T027O
