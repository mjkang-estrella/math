/-
Independent checks for `FiniteVariance.lean` (not part of the certificate;
used to demonstrate the theorem is applicable to arbitrary finite types,
including the empty type, and agrees with direct numeric evaluation).
-/
import FiniteVariance

open Finset

/-- The main theorem applies to the empty type: no fixed cardinality is
assumed anywhere. -/
example (K : Empty → Empty → ℝ) (u : Empty → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1) (hcol : ∀ j, ∑ i, K i j = 1) :
    (∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k) ^ 2)
      = 2 * ((∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2)) :=
  bistochastic_variance hrow hcol

/-- The deficit corollary applies to the empty type as well. -/
example (K : Empty → Empty → ℝ) (u : Empty → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1) (hcol : ∀ j, ∑ i, K i j = 1)
    (hK : ∀ i j, 0 ≤ K i j) :
    0 ≤ (∑ i, u i ^ 2) - (∑ j, (∑ i, K i j * u i) ^ 2) :=
  variance_deficit_nonneg hrow hcol hK

/-- Concrete `Fin 2` instance: `K` is the uniform bistochastic kernel
`K i j = 1/2`, `u 0 = 1`, `u 1 = 3`. -/
noncomputable def K2 : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

noncomputable def u2 : Fin 2 → ℝ := fun i => 1 + 2 * (i : ℝ)

theorem K2_row : ∀ i, ∑ j, K2 i j = 1 := by
  intro i
  have h := Fin.sum_univ_two (fun j : Fin 2 => K2 i j)
  rw [h]; simp only [K2]; norm_num

theorem K2_col : ∀ j, ∑ i, K2 i j = 1 := by
  intro j
  have h := Fin.sum_univ_two (fun i : Fin 2 => K2 i j)
  rw [h]; simp only [K2]; norm_num

theorem K2_nonneg : ∀ i j, 0 ≤ K2 i j := by
  intro i j; simp only [K2]; norm_num

/-- The concrete instance satisfies the identity, derived from the theorem. -/
example :
    (∑ j, ∑ i, ∑ k, K2 i j * K2 k j * (u2 i - u2 k) ^ 2)
      = 2 * ((∑ i, u2 i ^ 2) - (∑ j, (∑ i, K2 i j * u2 i) ^ 2)) :=
  bistochastic_variance K2_row K2_col

/-- The same concrete identity, verified by direct numeric evaluation with no
use of `bistochastic_variance` — confirming the theorem statement is not
vacuous and its orientation is as expected (both sides equal 4 here). -/
example :
    (∑ j, ∑ i, ∑ k, K2 i j * K2 k j * (u2 i - u2 k) ^ 2)
      = 2 * ((∑ i, u2 i ^ 2) - (∑ j, (∑ i, K2 i j * u2 i) ^ 2)) := by
  simp only [K2, u2, Fin.sum_univ_two]
  norm_num

/-- The concrete deficit is nonnegative, derived from the corollary. -/
example : 0 ≤ (∑ i, u2 i ^ 2) - (∑ j, (∑ i, K2 i j * u2 i) ^ 2) :=
  variance_deficit_nonneg K2_row K2_col K2_nonneg

/-- The concrete deficit value, by direct evaluation. -/
example : (∑ i, u2 i ^ 2) - (∑ j, (∑ i, K2 i j * u2 i) ^ 2) = 2 := by
  simp only [K2, u2, Fin.sum_univ_two]
  norm_num

#print axioms K2_row
#print axioms K2_col
#print axioms K2_nonneg
