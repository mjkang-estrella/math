import MatrixRelation
import CoordinateRelation
import Mathlib.RingTheory.Ideal.Maps
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace TraceFormal
open MvPolynomial
def e36 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * B * A * B) - tr (B * B * A * A * B * A)
def e37 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * C * C * A * C) - tr (C * C * A * A * C * A)
def e38 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * C * C * B * C) - tr (C * C * B * B * C * B)
def e39 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * A * B * C) + tr (A * A * B * A * C * B) + tr (A * A * C * A * B * B) - tr (A * A * B * B * A * C) - tr (A * A * B * C * A * B) - tr (A * A * C * B * A * B)
def e40 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * A * B * A * C) + tr (B * B * A * B * C * A) + tr (B * B * C * B * A * A) - tr (B * B * A * A * B * C) - tr (B * B * A * C * B * A) - tr (B * B * C * A * B * A)
def e41 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * C * B * C * B * A) + tr (C * C * B * C * A * B) + tr (C * C * A * C * B * B) - tr (C * C * B * B * C * A) - tr (C * C * B * A * C * B) - tr (C * C * A * B * C * B)
def e42 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * C * A * C * B) + tr (A * A * C * A * B * C) + tr (A * A * B * A * C * C) - tr (A * A * C * C * A * B) - tr (A * A * C * B * A * C) - tr (A * A * B * C * A * C)
def e43 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (B * B * C * B * C * A) + tr (B * B * C * B * A * C) + tr (B * B * A * B * C * C) - tr (B * B * C * C * A * B) - tr (B * B * C * A * B * C) - tr (B * B * C * A * C * B)
def e44 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (C * C * A * C * A * B) + tr (C * C * A * C * B * A) + tr (C * C * B * C * A * A) - tr (C * C * A * A * C * B) - tr (C * C * A * B * C * A) - tr (C * C * B * A * C * A)
def e45 {K : Type*} [CommRing K] (A B C : Mat K) : K :=
  tr (A * A * B * B * C * C) + tr (A * A * C * B * C * B) + tr (A * B * A * C * C * B) + tr (A * B * C * A * B * C) + tr (A * C * A * C * B * B) - tr (A * A * B * C * B * C) - tr (A * A * C * C * B * B) - tr (A * B * A * B * C * C) - tr (A * B * B * C * A * C) - tr (A * C * B * A * C * B)
def sourceE {K : Type*} [CommRing K] (A B C : Mat K) (i : ℕ) : K :=
  match i with
  | 36 => e36 A B C
  | 37 => e37 A B C
  | 38 => e38 A B C
  | 39 => e39 A B C
  | 40 => e40 A B C
  | 41 => e41 A B C
  | 42 => e42 A B C
  | 43 => e43 A B C
  | 44 => e44 A B C
  | 45 => e45 A B C
  | _ => actualE A B C i

def centered {K : Type*} [Field K] (A : Mat K) : Mat K :=
  A - (tr A / 3) • (1 : Mat K)

theorem centered_tr {K : Type*} [Field K] [CharZero K] (A : Mat K) :
    tr (centered A) = 0 := by
  simp [centered, tr, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]

abbrev CE (K : Type*) [CommRing K] := MvPolynomial (Fin 48) K
/-- The 45 printed centered generators, followed by tr(X), tr(Y), tr(Z). -/
def sourceValues {K : Type*} [Field K] (A B C : Mat K) (i : Fin 48) : K :=
  if i.val < 45 then sourceE (centered A) (centered B) (centered C) (i.val + 1)
  else if i.val = 45 then tr A else if i.val = 46 then tr B else tr C

noncomputable def relation48 {K : Type*} [CommRing K] : CE K :=
  X 0 * X 34 + X 3 * X 33 + X 4 * X 32 - 2 * X 6 * X 19 +
  2 * X 9 * X 22 + 2 * X 10 * X 21 - 2 * X 11 * X 18 -
  2 * X 13 * X 17 + X 15 * X 20 - 3 * X 16 * X 23

theorem relation48_eval {K : Type*} [Field K] [CharZero K] (A B C : Mat K) :
    eval (sourceValues A B C) relation48 = 0 := by
  simpa [relation48, sourceValues, sourceE, relation6, actualE] using
    relation6_matrix (centered A) (centered B) (centered C)
      (centered_tr A) (centered_tr B) (centered_tr C)

theorem relation48_ne_zero {K : Type*} [Field K] [CharZero K] :
    (relation48 : CE K) ≠ 0 := by
  intro h
  have hh := congrArg (eval (fun i : Fin 48 =>
    if i.val = 0 then (6 : K) else if i.val = 34 then 1 else 0)) h
  norm_num [relation48] at hh

/-- Genuine simultaneous evaluation on every triple of full matrices. -/
noncomputable def matrixInterpretation {K : Type*} [Field K] :
    CE K →+* ((Mat K × Mat K × Mat K) → K) where
  toFun p m := eval (sourceValues m.1 m.2.1 m.2.2) p
  map_one' := by funext m; exact map_one _
  map_mul' a b := by funext m; exact map_mul _ a b
  map_zero' := by funext m; exact map_zero _
  map_add' a b := by funext m; exact map_add _ a b

noncomputable def actualIdeal {K : Type*} [Field K] : Ideal (CE K) :=
  RingHom.ker matrixInterpretation

/-- A nonzero literal polynomial in the actual full-matrix specialization kernel.
This theorem does not assert that the source fixed tuple list fails to generate. -/
theorem literal_nonzero_matrix_relation {K : Type*} [Field K] [CharZero K] :
    (relation48 : CE K) ≠ 0 ∧ (relation48 : CE K) ∈ actualIdeal := by
  refine ⟨relation48_ne_zero, ?_⟩
  change matrixInterpretation relation48 = 0
  funext m
  exact relation48_eval m.1 m.2.1 m.2.2
#print axioms literal_nonzero_matrix_relation
end TraceFormal
