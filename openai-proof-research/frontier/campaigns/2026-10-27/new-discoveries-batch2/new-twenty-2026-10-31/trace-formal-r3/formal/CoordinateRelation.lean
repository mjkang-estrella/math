import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace TraceCE
open MvPolynomial
noncomputable def relation {K : Type*} [CommRing K] : MvPolynomial ℕ K :=
  X 1 * X 35 + X 4 * X 34 + X 5 * X 33 - 2 * X 7 * X 20 +
  2 * X 10 * X 23 + 2 * X 11 * X 22 - 2 * X 12 * X 19 -
  2 * X 14 * X 18 + X 16 * X 21 - 3 * X 17 * X 24

def separator {K : Type*} [CommRing K] (i : ℕ) : K :=
  if i = 1 then 6 else if i = 35 then 1 else 0

theorem separating_evaluation {K : Type*} [CommRing K] :
    eval (separator : ℕ → K) relation = 6 := by
  norm_num [relation, separator]

theorem relation_ne_zero {K : Type*} [CommRing K] [CharZero K] :
    (relation : MvPolynomial ℕ K) ≠ 0 := by
  intro h
  have hh := separating_evaluation (K := K)
  rw [h, map_zero] at hh
  exact (by norm_num : (0 : K) ≠ 6) hh
#print axioms relation_ne_zero
end TraceCE
