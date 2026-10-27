import SmaleCounterexample

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarSmale

open Polynomial

def sourcePolynomial {A : Type*} [CommRing A] {n : ℕ} (a : Fin n → A) : Polynomial A :=
  ∏ j, (X - C (a j))

def SourceClaim : Prop :=
  ∀ (A : Type) [CommCStarAlgebra A] (n : ℕ), 2 ≤ n →
    ∀ (a : Fin n → A) (z : A), (sourcePolynomial a).derivative.eval z ≠ 0 →
      ∃ w : A, (sourcePolynomial a).derivative.eval w = 0 ∧
        ‖(sourcePolynomial a).eval z - (sourcePolynomial a).eval w‖ / ‖z - w‖ ≤
          ‖(sourcePolynomial a).derivative.eval z‖

theorem sourcePolynomial_cubic {A : Type*} [CommRing A] (a : Fin 3 → A) :
    sourcePolynomial a = cubicPolynomial a := by
  simp [sourcePolynomial, cubicPolynomial, Fin.prod_univ_succ]
  ring

theorem cubicPolynomial_monic {A : Type*} [CommRing A] (a : Fin 3 → A) :
    (cubicPolynomial a).Monic :=
  ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem cubicPolynomial_degree {A : Type*} [CommRing A] [Nontrivial A] (a : Fin 3 → A) :
    (cubicPolynomial a).natDegree = 3 := by
  unfold cubicPolynomial
  rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp

theorem sourceClaim_implies_cubic (h : SourceClaim) : SourceCubicClaim FunctionAlgebra := by
  intro a z hz
  have h' := h FunctionAlgebra 3 (by norm_num) a z
  simp only [sourcePolynomial_cubic, cubicPolynomial_eval, cubicPolynomial_deleted] at h'
  exact h' hz

theorem source_counterexample : ¬SourceClaim :=
  fun h => source_counterexample_cubic (sourceClaim_implies_cubic h)

theorem both_critical_branches :
    cubicDeleted roots branch = 0 ∧ cubicDeleted roots (-branch) = 0 := by
  constructor <;> rw [deleted_eq] <;> ring

theorem derivative_explicit_inverse :
    cubicDeleted roots coordinate * ContinuousMap.const Time (-16 / 3 : ℂ) = 1 := by
  rw [deleted_coordinate]
  ext t
  change (-3 / 16 : ℂ) * (-16 / 3) = 1
  norm_num

end CStarSmale
