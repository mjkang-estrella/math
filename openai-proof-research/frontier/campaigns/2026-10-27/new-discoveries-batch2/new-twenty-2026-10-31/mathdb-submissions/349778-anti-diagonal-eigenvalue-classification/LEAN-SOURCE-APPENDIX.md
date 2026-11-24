# Lean source appendix

Status: COMPLETE. All modules, including the unconditional classification endpoint, appear in dependency order.

### `ClassificationDefinitions.lean`

```lean
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Basic

namespace Classification349778

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def LowerTriangular {n : ℕ} (A : Mat n) : Prop := ∀ i j, i < j → A i j = 0

def Stochastic {n : ℕ} (A : Mat n) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1

def pascal (n : ℕ) : Mat n := fun i j => (Nat.choose i.val j.val : ℝ)

def pascalInv (n : ℕ) : Mat n :=
  fun i j => (-1 : ℝ) ^ (i.val + j.val) * (Nat.choose i.val j.val : ℝ)

noncomputable def reversal (n : ℕ) : Mat n := fun i j => if i = j.rev then 1 else 0

noncomputable def binomialTransform {n : ℕ} (a : Vec n) : Mat n :=
  pascal n * Matrix.diagonal a * (pascal n)⁻¹

def leading {n : ℕ} (A : Mat n) (m : ℕ) (h : m ≤ n) : Mat m :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

noncomputable def signedDiagonal {n : ℕ} (A : Mat n) : Vec n :=
  fun i => (-1 : ℝ) ^ i.val * A i i

noncomputable def prescribedCharpoly {n : ℕ} (A : Mat n) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (signedDiagonal A i))

def GlobalAntiDiagonalCharpoly {n : ℕ} (A : Mat n) : Prop :=
  ∀ (m : ℕ) (h : m ≤ n),
    ((leading A m h) * reversal m).charpoly = prescribedCharpoly (leading A m h)

def Diagonalizable {n : ℕ} (A : Mat n) : Prop :=
  ∃ (Q : Mat n) (a : Vec n), IsUnit Q.det ∧ A * Q = Q * Matrix.diagonal a

def HasRealSpectrum {n : ℕ} (A : Mat n) (a : Vec n) : Prop :=
  (A.map Complex.ofRealHom).charpoly.roots = (Finset.univ.val.map (fun i => (a i : ℂ)))

def AntiDiagonalEigenvalue {n : ℕ} (A : Mat n) : Prop :=
  LowerTriangular A ∧ Diagonalizable A ∧ HasRealSpectrum (A * reversal n) (signedDiagonal A)

def GlobalAntiDiagonalEigenvalue {n : ℕ} (A : Mat n) : Prop :=
  LowerTriangular A ∧ ∀ (m : ℕ) (h : m ≤ n), AntiDiagonalEigenvalue (leading A m h)

def DistinctEigenvalues {n : ℕ} (A : Mat n) : Prop :=
  ∃ a : Fin n → ℂ, Function.Injective a ∧
    (A.map Complex.ofRealHom).charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i))

def MathDB349778 : Prop :=
  ∀ (n : ℕ) (A : Mat n), Stochastic A → DistinctEigenvalues A →
    (GlobalAntiDiagonalEigenvalue A ↔ ∃ a : Vec n, A = binomialTransform a)

def binomialVector (n k : ℕ) : Vec n := fun i => (Nat.choose i.val k : ℝ)

def difference (n : ℕ) (v : Vec (n+1)) : Vec n := fun i => v i.succ - v i.castSucc

noncomputable def flag (n d : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range (fun k : Fin (d+1) => binomialVector n k.val))

def KnownRowsHarmonic {N : ℕ} (H : Mat N) (a : ℝ) (u : Vec N) : Prop :=
  ∀ i : Fin N, i.val + 1 < N → ((H * reversal N).mulVec u) i = a * u i

end Classification349778
```

### `ClassificationSanity.lean`

```lean
import ClassificationDefinitions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

namespace Classification349778

open Matrix
open scoped Matrix

 theorem pascal_two : pascal 2 = !![1, 0; 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [pascal]

 theorem pascalInv_two : pascalInv 2 = !![1, 0; -1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [pascalInv]

 theorem pascal_three : pascal 3 = !![1, 0, 0; 1, 1, 0; 1, 2, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [pascal]

 theorem pascalInv_three : pascalInv 3 = !![1, 0, 0; -1, 1, 0; 1, -2, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [pascalInv]

 theorem pascal_inv_two : (pascal 2)⁻¹ = pascalInv 2 := by
  apply Matrix.inv_eq_right_inv
  rw [pascal_two, pascalInv_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

 theorem pascal_inv_three : (pascal 3)⁻¹ = pascalInv 3 := by
  apply Matrix.inv_eq_right_inv
  rw [pascal_three, pascalInv_three]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

 theorem transform_two (a b : ℝ) :
    binomialTransform ![a,b] = !![a, 0; a-b, b] := by
  rw [binomialTransform, pascal_inv_two, pascal_two, pascalInv_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail, Matrix.diagonal, Fin.sum_univ_succ]; ring

 theorem transform_three (a b c : ℝ) :
    binomialTransform ![a,b,c] = !![a, 0, 0; a-b, b, 0; a-2*b+c, 2*(b-c), c] := by
  rw [binomialTransform, pascal_inv_three, pascal_three, pascalInv_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail, Matrix.diagonal, Fin.sum_univ_succ] <;> ring

-- The old parameters of the source's Example 2.5.
 theorem source_parameters_three :
    binomialTransform ![(1:ℝ), 2/3, 1/4] =
      !![1, 0, 0; 1/3, 2/3, 0; -1/12, 5/6, 1/4] := by
  rw [transform_three]; norm_num

 theorem source_negative_entry :
    binomialTransform ![(1:ℝ), 2/3, 1/4] 2 0 = -1/12 := by
  rw [source_parameters_three]; norm_num

 theorem source_row_sums : ∀ i : Fin 3,
    ∑ j, binomialTransform ![(1:ℝ), 2/3, 1/4] i j = 1 := by
  intro i; rw [source_parameters_three]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

 theorem reversal_two : reversal 2 = !![(0:ℝ),1;1,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [reversal, Fin.rev]

 theorem transform_two_charpoly (a b : ℝ) :
    ((binomialTransform ![a,b]) * reversal 2).charpoly =
      (Polynomial.X - Polynomial.C a) * (Polynomial.X + Polynomial.C b) := by
  rw [transform_two, reversal_two, Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ,
    Polynomial.C_sub, Polynomial.C_mul]
  ring

#print axioms source_parameters_three
#print axioms transform_two_charpoly
end Classification349778
```

### `ClassificationDifference.lean`

```lean
import ClassificationDefinitions
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Classification349778

theorem pascal_lower (n : ℕ) : LowerTriangular (pascal n) := by
  intro i j h
  simp [pascal, Nat.choose_eq_zero_of_lt h]

theorem pascalInv_lower (n : ℕ) : LowerTriangular (pascalInv n) := by
  intro i j h
  simp [pascalInv, Nat.choose_eq_zero_of_lt h]

theorem pascal_diagonal (n : ℕ) (i : Fin n) : pascal n i i = 1 := by
  simp [pascal]

theorem pascalInv_diagonal (n : ℕ) (i : Fin n) : pascalInv n i i = 1 := by
  simp only [pascalInv, Nat.choose_self, Nat.cast_one, mul_one]
  rw [← two_mul, pow_mul]
  norm_num

theorem reversal_mulVec {n : ℕ} (v : Vec n) (i : Fin n) :
    (reversal n).mulVec v i = v i.rev := by
  classical
  simp only [Matrix.mulVec, dotProduct, reversal]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro j _ hj
    have : i ≠ j.rev := by
      intro h
      apply hj
      simpa using congrArg Fin.rev h.symm
    simp [this]
  · simp

theorem reversal_sq (n : ℕ) : reversal n * reversal n = 1 := by
  classical
  ext i j
  change (reversal n).mulVec (fun k => reversal n k j) i = _
  rw [reversal_mulVec]
  simp only [reversal, Matrix.one_apply]
  have : i.rev = j.rev ↔ i = j := Fin.rev_injective.eq_iff
  simp [this]

theorem difference_binomial_zero (n : ℕ) : difference n (binomialVector (n+1) 0) = 0 := by
  ext i
  simp [difference, binomialVector]

theorem difference_binomial_succ (n k : ℕ) :
    difference n (binomialVector (n+1) (k+1)) = binomialVector n k := by
  ext i
  simp only [difference, binomialVector, Fin.val_succ, Fin.val_castSucc]
  rw [Nat.choose_succ_succ, Nat.cast_add]
  ring

theorem difference_add (n : ℕ) (u v : Vec (n+1)) :
    difference n (u+v) = difference n u + difference n v := by
  ext i; simp [difference]; ring

theorem difference_smul (n : ℕ) (c : ℝ) (u : Vec (n+1)) :
    difference n (c • u) = c • difference n u := by
  ext i; simp [difference]; ring

theorem difference_reversal (n : ℕ) (v : Vec (n+1)) :
    difference n ((reversal (n+1)).mulVec v) =
      -(reversal n).mulVec (difference n v) := by
  ext i
  simp only [difference, reversal_mulVec, Pi.neg_apply]
  have h₁ : i.succ.rev = i.rev.castSucc := by apply Fin.ext; simp [Fin.rev]
  have h₂ : i.castSucc.rev = i.rev.succ := by apply Fin.ext; simp [Fin.rev]; omega
  rw [h₁, h₂]
  ring

theorem difference_constant (n : ℕ) (c : ℝ) : difference n (fun _ => c) = 0 := by
  ext i; simp [difference]

theorem difference_eq_zero_iff (n : ℕ) (v : Vec (n+1)) :
    difference n v = 0 ↔ ∃ c, v = fun _ => c := by
  constructor
  · intro h
    refine ⟨v 0, ?_⟩
    funext i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hh := congrFun h i
      simp only [difference, Pi.zero_apply, sub_eq_zero] at hh
      exact hh.trans ih
  · rintro ⟨c, rfl⟩
    exact difference_constant n c

-- Removing a final-row perturbation commutes with one difference on all known rows.
theorem difference_last_support (n : ℕ) (v : Vec (n+2))
    (h : ∀ i : Fin (n+2), i.val + 1 < n+2 → v i = 0) :
    ∀ i : Fin (n+1), i.val + 1 < n+1 → difference (n+1) v i = 0 := by
  intro i hi
  rw [difference, h i.succ (by simp; omega), h i.castSucc (by simp; omega)]
  ring

#print axioms reversal_sq
#print axioms difference_reversal
#print axioms difference_eq_zero_iff
end Classification349778
```

### `ClassificationPascal.lean`

```lean
import ClassificationDifference
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

lemma alternating_choose (n : ℕ) :
    (∑ k ∈ range (n+1), (-1 : ℝ)^k * (Nat.choose n k : ℝ)) =
      if n = 0 then 1 else 0 := by
  exact_mod_cast (Int.alternating_sum_range_choose (n := n))

lemma binomial_inverse_sum (m i j : ℕ) (hi : i < m) :
    (∑ k ∈ range m, (Nat.choose i k : ℝ) *
      ((-1 : ℝ)^(k+j) * (Nat.choose k j : ℝ))) = if i=j then 1 else 0 := by
  classical
  by_cases hji : j ≤ i
  · have hreindex :
        (∑ k ∈ range m, (Nat.choose i k : ℝ) *
          ((-1 : ℝ)^(k+j) * (Nat.choose k j : ℝ))) =
        ∑ t ∈ range (i-j+1), (Nat.choose i (j+t) : ℝ) *
          ((-1 : ℝ)^(j+t+j) * (Nat.choose (j+t) j : ℝ)) := by
      symm
      apply Finset.sum_bij_ne_zero (fun t _ _ => j+t)
      · intro t ht _; simp only [mem_range] at *; omega
      · intro t ht _ s hs _ heq; omega
      · intro k hk hk0
        have hk1 : j ≤ k := by
          by_contra h
          simp [Nat.choose_eq_zero_of_lt (show k<j by omega)] at hk0
        have hk2 : k ≤ i := by
          by_contra h
          simp [Nat.choose_eq_zero_of_lt (show i<k by omega)] at hk0
        refine ⟨k-j, by simp only [mem_range]; omega, ?_, by omega⟩
        simpa [show j+(k-j)=k by omega] using hk0
      · intro t _ _; rfl
    rw [hreindex]
    have hterm : ∀ t, (Nat.choose i (j+t) : ℝ) *
        ((-1 : ℝ)^(j+t+j) * (Nat.choose (j+t) j : ℝ)) =
        (Nat.choose i j : ℝ) * ((-1 : ℝ)^t * (Nat.choose (i-j) t : ℝ)) := by
      intro t
      have hc : (Nat.choose i (j+t) : ℝ) * (Nat.choose (j+t) j : ℝ) =
          (Nat.choose i j : ℝ) * (Nat.choose (i-j) t : ℝ) := by
        exact_mod_cast (by simpa using (Nat.choose_mul (n := i) (k := j+t) (s := j) (by omega)))
      have hp : (-1 : ℝ)^(j+t+j) = (-1 : ℝ)^t := by
        rw [show j+t+j = 2*j+t by omega, pow_add, pow_mul]
        norm_num
      rw [hp]
      calc
        _ = (-1 : ℝ)^t * ((Nat.choose i (j+t) : ℝ) * (Nat.choose (j+t) j : ℝ)) := by ring
        _ = _ := by rw [hc]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, alternating_choose]
    by_cases he : i=j
    · subst i; simp
    · simp [show i-j ≠ 0 by omega, he]
  · rw [ite_eq_right (show i ≠ j by omega)]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i < k
    · simp [Nat.choose_eq_zero_of_lt hik]
    · simp [Nat.choose_eq_zero_of_lt (show k < j by omega)]

theorem pascal_mul_pascalInv (n : ℕ) : pascal n * pascalInv n = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, pascal, pascalInv, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (Nat.choose i.val k : ℝ) *
    ((-1 : ℝ)^(k+j.val) * (Nat.choose k j.val : ℝ))) n]
  simpa only [Fin.ext_iff] using binomial_inverse_sum n i.val j.val i.isLt

theorem pascalInv_mul_pascal (n : ℕ) : pascalInv n * pascal n = 1 :=
  mul_eq_one_comm.mp (pascal_mul_pascalInv n)

theorem pascal_inv (n : ℕ) : (pascal n)⁻¹ = pascalInv n :=
  Matrix.inv_eq_right_inv (pascal_mul_pascalInv n)

#print axioms pascal_inv
end Classification349778
```

### `ClassificationTransform.lean`

```lean
import ClassificationPascal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

lemma lower_mul {n : ℕ} {A B : Mat n} (hA : LowerTriangular A)
    (hB : LowerTriangular B) : LowerTriangular (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (by omega), mul_zero]

lemma lower_diag_mul {n : ℕ} {A B : Mat n}
    (hA : LowerTriangular A) (hB : LowerTriangular B) (i : Fin n) :
    (A*B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    by_cases hik : i < k
    · rw [hA i k hik, zero_mul]
    · rw [hB k i (by omega), mul_zero]
  · simp

theorem transform_entry {n : ℕ} (a : Vec n) (i j : Fin n) :
    binomialTransform a i j = ∑ k, (Nat.choose i.val k.val : ℝ) * a k *
      ((-1 : ℝ)^(k.val+j.val) * (Nat.choose k.val j.val : ℝ)) := by
  rw [binomialTransform, pascal_inv, Matrix.mul_apply]
  simp [Matrix.mul_diagonal, pascal, pascalInv]

theorem transform_lower {n : ℕ} (a : Vec n) : LowerTriangular (binomialTransform a) := by
  rw [binomialTransform, pascal_inv]
  apply lower_mul (lower_mul (pascal_lower n) ?_) (pascalInv_lower n)
  intro i j hij
  simp [Matrix.diagonal, ne_of_lt hij]

theorem transform_diag {n : ℕ} (a : Vec n) (i : Fin n) : binomialTransform a i i = a i := by
  rw [binomialTransform, pascal_inv]
  have hd : LowerTriangular (Matrix.diagonal a) := by
    intro i j hij; simp [Matrix.diagonal, ne_of_lt hij]
  rw [lower_diag_mul (lower_mul (pascal_lower n) hd) (pascalInv_lower n),
    lower_diag_mul (pascal_lower n) hd]
  simp [pascal_diagonal, pascalInv_diagonal]

theorem transform_mul_pascal {n : ℕ} (a : Vec n) :
    binomialTransform a * pascal n = pascal n * Matrix.diagonal a := by
  rw [binomialTransform, pascal_inv, Matrix.mul_assoc, pascalInv_mul_pascal,
    Matrix.mul_one]

theorem transform_binomialVector {n : ℕ} (a : Vec n) (k : Fin n) :
    (binomialTransform a).mulVec (binomialVector n k.val) = a k • binomialVector n k.val := by
  funext i
  have h := congrArg (fun M : Mat n => M i k) (transform_mul_pascal a)
  simpa [Matrix.mul_diagonal, Matrix.mul_apply, Matrix.diagonal, binomialVector, pascal,
    Matrix.mulVec, dotProduct, mul_comm] using h

theorem transform_row_sum {n : ℕ} (a : Vec (n+1)) (i : Fin (n+1)) :
    ∑ j, binomialTransform a i j = a 0 := by
  have h := congrFun (transform_binomialVector a 0) i
  simpa [Matrix.mulVec, dotProduct, binomialVector] using h

theorem binomial_expansion {n : ℕ} (v : Vec n) :
    ∃ c : Vec n, v = (pascal n).mulVec c := by
  refine ⟨(pascalInv n).mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec, pascal_mul_pascalInv, Matrix.one_mulVec]

theorem binomial_basis (n : ℕ) :
    LinearIndependent ℝ (fun k : Fin n => binomialVector n k.val) := by
  change LinearIndependent ℝ (pascal n).col
  apply Matrix.mulVec_injective_iff.mp
  intro u v h
  have hh := congrArg ((pascalInv n).mulVec) h
  simpa only [Matrix.mulVec_mulVec, pascalInv_mul_pascal, Matrix.one_mulVec] using hh

/-- All binomial transforms are genuinely real diagonalizable, even at repeated parameters. -/
theorem transform_diagonalizable {n : ℕ} (a : Vec n) : Diagonalizable (binomialTransform a) := by
  refine ⟨pascal n, a, ?_, transform_mul_pascal a⟩
  have hd := congrArg Matrix.det (pascal_mul_pascalInv n)
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact isUnit_iff_ne_zero.mpr (by intro h; rw [h, zero_mul] at hd; exact zero_ne_one hd)

#print axioms transform_entry
#print axioms transform_binomialVector
#print axioms binomial_basis
#print axioms transform_diagonalizable
end Classification349778
```

### `ClassificationIntertwining.lean`

```lean
import ClassificationTransform

set_option linter.unusedSimpArgs false
namespace Classification349778

noncomputable def differenceLin (n : ℕ) : Vec (n+1) →ₗ[ℝ] Vec n where
  toFun := difference n
  map_add' := difference_add n
  map_smul' := difference_smul n

def iterDifference (n : ℕ) : (j : ℕ) → Vec (n+j) → Vec n
  | 0 => fun v => v
  | j+1 => fun v => iterDifference n j (difference (n+j) v)

theorem pascal_mulVec_eq_sum {n : ℕ} (c : Vec n) :
    (pascal n).mulVec c = ∑ k, c k • binomialVector n k.val := by
  ext i
  simp [Matrix.mulVec, dotProduct, pascal, binomialVector, Finset.sum_apply, mul_comm]

theorem binomial_expansion_sum {n : ℕ} (v : Vec n) :
    ∃ c : Vec n, v = ∑ k, c k • binomialVector n k.val := by
  obtain ⟨c, hc⟩ := binomial_expansion v
  exact ⟨c, hc.trans (pascal_mulVec_eq_sum c)⟩

theorem difference_sum_binomial {n : ℕ} (c : Vec (n+1)) :
    difference n (∑ k, c k • binomialVector (n+1) k.val) =
      ∑ k : Fin n, c k.succ • binomialVector n k.val := by
  change differenceLin n (∑ k, c k • binomialVector (n+1) k.val) = _
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_smul, differenceLin, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.val_zero, difference_binomial_zero, smul_zero, zero_add, Fin.val_succ,
    difference_binomial_succ]

theorem transform_sum_binomial {n : ℕ} (a c : Vec n) :
    (binomialTransform a).mulVec (∑ k, c k • binomialVector n k.val) =
      ∑ k, (c k * a k) • binomialVector n k.val := by
  change (binomialTransform a).mulVecLin (∑ k, c k • binomialVector n k.val) = _
  rw [map_sum]
  simp only [map_smul, Matrix.coe_mulVecLin, transform_binomialVector, smul_smul]

theorem difference_transform {n : ℕ} (a : Vec (n+1)) (v : Vec (n+1)) :
    difference n ((binomialTransform a).mulVec v) =
      (binomialTransform (fun i => a i.succ)).mulVec (difference n v) := by
  obtain ⟨c, rfl⟩ := binomial_expansion_sum v
  rw [transform_sum_binomial, difference_sum_binomial, difference_sum_binomial,
    transform_sum_binomial]

theorem difference_transform_reversal {n : ℕ} (a : Vec (n+1)) (v : Vec (n+1)) :
    difference n (((binomialTransform a) * reversal (n+1)).mulVec v) =
      -((binomialTransform (fun i => a i.succ)) * reversal n).mulVec (difference n v) := by
  rw [← Matrix.mulVec_mulVec, difference_transform, difference_reversal,
    Matrix.mulVec_neg, Matrix.mulVec_mulVec]

theorem iterDifference_last_support (N j : ℕ) (v : Vec (N+j))
    (h : ∀ i : Fin (N+j), i.val+1 < N+j → v i = 0) :
    ∀ i : Fin N, i.val+1 < N → iterDifference N j v i = 0 := by
  induction j with
  | zero => exact h
  | succ j ih =>
    apply ih (difference (N+j) v)
    intro i hi
    dsimp [difference]
    rw [h i.succ (by simp; omega), h i.castSucc (by simp; omega)]
    ring

#print axioms difference_transform
#print axioms difference_transform_reversal
#print axioms iterDifference_last_support
end Classification349778
```

### `ClassificationFlag.lean`

```lean
import ClassificationIntertwining
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.unusedSimpArgs false
namespace Classification349778

lemma flag_mem_iff {n d : ℕ} (v : Vec n) :
    v ∈ flag n d ↔ ∃ c : Fin (d+1) → ℝ,
      (∑ k, c k • binomialVector n k.val) = v := by
  exact Submodule.mem_span_range_iff_exists_fun ℝ

theorem flag_binomial {n d : ℕ} (k : Fin (d+1)) : binomialVector n k.val ∈ flag n d :=
  Submodule.subset_span ⟨k, rfl⟩

theorem flag_finrank {n d : ℕ} (hd : d < n) : Module.finrank ℝ (flag n d) = d+1 := by
  have hi : LinearIndependent ℝ (fun k : Fin (d+1) => binomialVector n k.val) :=
    (binomial_basis n).comp (Fin.castLE (by omega)) (Fin.castLE_injective _)
  unfold flag
  rw [finrank_span_eq_card hi]
  simp

theorem flag_transform {n d : ℕ} (hd : d < n) (a : Vec n) (v : Vec n)
    (hv : v ∈ flag n d) : (binomialTransform a).mulVec v ∈ flag n d := by
  obtain ⟨c, rfl⟩ := (flag_mem_iff v).mp hv
  change (binomialTransform a).mulVecLin (∑ k, c k • binomialVector n k.val) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro k _
  rw [map_smul]
  have h := transform_binomialVector a (Fin.castLE (show d+1 ≤ n by omega) k)
  change (binomialTransform a).mulVec (binomialVector n k.val) = _ at h
  rw [Matrix.coe_mulVecLin, h]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (flag_binomial k))

/-- The flag is determined by its first d+1 coordinates. -/
theorem flag_zero_of_leading_zero {n d : ℕ} (h : d+1 ≤ n) (v : Vec n)
    (hv : v ∈ flag n d) (hz : ∀ i : Fin (d+1), v (Fin.castLE h i) = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := (flag_mem_iff v).mp hv
  have hc : (pascal (d+1)).mulVec c = 0 := by
    ext i
    have hh := hz i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, binomialVector, pascal,
      mul_comm] using hh
  have hc0 : c = 0 := by
    have := congrArg ((pascalInv (d+1)).mulVec) hc
    simpa only [Matrix.mulVec_mulVec, pascalInv_mul_pascal, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this
  simp [hc0]

/-- Interpolate arbitrary values on the first d+1 coordinates by a unique flag vector. -/
theorem flag_restrict_bijective {n d : ℕ} (h : d+1 ≤ n) :
    Function.Bijective (fun v : flag n d =>
      (fun i : Fin (d+1) => (v : Vec n) (Fin.castLE h i))) := by
  constructor
  · intro v w hEq
    apply Subtype.ext
    have hz : (v : Vec n) - w = 0 := by
      apply flag_zero_of_leading_zero h _ (Submodule.sub_mem _ v.property w.property)
      intro i
      exact sub_eq_zero.mpr (congrFun hEq i)
    exact sub_eq_zero.mp hz
  · intro w
    let c := (pascalInv (d+1)).mulVec w
    let v : Vec n := ∑ k : Fin (d+1), c k • binomialVector n k.val
    refine ⟨⟨v, (flag_mem_iff v).mpr ⟨c, rfl⟩⟩, ?_⟩
    have hc : (pascal (d+1)).mulVec c = w := by
      dsimp [c]
      rw [Matrix.mulVec_mulVec, pascal_mul_pascalInv, Matrix.one_mulVec]
    funext i
    have := congrFun hc i
    simpa [v, Matrix.mulVec, dotProduct, Finset.sum_apply, binomialVector, pascal,
      mul_comm] using this

#print axioms flag_finrank
#print axioms flag_transform
#print axioms flag_restrict_bijective
end Classification349778
```

### `ClassificationFlagDifference.lean`

```lean
import ClassificationFlag

set_option linter.unusedSimpArgs false
namespace Classification349778

lemma smul_binomial_zero (n : ℕ) (c : ℝ) :
    c • binomialVector n 0 = fun _ => c := by
  ext i; simp [binomialVector]

lemma flag_constant {n d : ℕ} (c : ℝ) : (fun _ : Fin n => c) ∈ flag n d := by
  have h := Submodule.smul_mem (flag n d) c (flag_binomial (n := n) (0 : Fin (d+1)))
  change c • binomialVector n 0 ∈ flag n d at h
  rw [smul_binomial_zero] at h
  exact h

lemma flag_zero_iff {n : ℕ} (v : Vec n) : v ∈ flag n 0 ↔ ∃ c, v = fun _ => c := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := (flag_mem_iff v).mp hv
    refine ⟨c 0, ?_⟩
    have he : (∑ k : Fin 1, c k • binomialVector n k.val) =
        c 0 • binomialVector n 0 := by simp [Fin.sum_univ_succ]
    exact hc.symm.trans (he.trans (smul_binomial_zero n (c 0)))
  · rintro ⟨c, rfl⟩
    exact flag_constant c

theorem flag_difference_step {n d : ℕ} (v : Vec (n+1)) :
    v ∈ flag (n+1) (d+1) ↔ difference n v ∈ flag n d := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := (flag_mem_iff v).mp hv
    change differenceLin n (∑ k, c k • binomialVector (n+1) k.val) ∈ _
    rw [map_sum, Fin.sum_univ_succ]
    simp only [map_smul, differenceLin, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.val_zero, difference_binomial_zero, smul_zero, zero_add, Fin.val_succ,
      difference_binomial_succ]
    exact (flag_mem_iff _).mpr ⟨fun k => c k.succ, rfl⟩
  · intro hv
    obtain ⟨c, hc⟩ := (flag_mem_iff _).mp hv
    let u : Vec (n+1) := ∑ k : Fin (d+1), c k • binomialVector (n+1) (k.val+1)
    have hu : difference n u = difference n v := by
      change differenceLin n (∑ k : Fin (d+1), c k • binomialVector (n+1) (k.val+1)) = _
      rw [map_sum]
      simpa only [map_smul, differenceLin, LinearMap.coe_mk, AddHom.coe_mk,
        difference_binomial_succ] using hc
    have hsub : difference n (v-u) = 0 := by
      change differenceLin n (v-u) = _
      rw [map_sub]
      change difference n v - difference n u = 0
      rw [hu, sub_self]
    obtain ⟨b, hb⟩ := (difference_eq_zero_iff n (v-u)).mp hsub
    have humem : u ∈ flag (n+1) (d+1) := by
      apply Submodule.sum_mem
      intro k _
      exact Submodule.smul_mem _ _ (flag_binomial k.succ)
    have hvmem := Submodule.add_mem (flag (n+1) (d+1)) (flag_constant b) humem
    rw [← hb, sub_add_cancel] at hvmem
    exact hvmem

theorem flag_difference (N j : ℕ) (_hN : 0 < N) (v : Vec (N+j)) :
    v ∈ flag (N+j) j ↔ ∃ c, iterDifference N j v = fun _ => c := by
  induction j with
  | zero => exact flag_zero_iff v
  | succ j ih =>
    exact (flag_difference_step (n := N+j) (d := j) v).trans
      (ih (difference (N+j) v))

#print axioms flag_difference_step
#print axioms flag_difference
end Classification349778
```

### `ClassificationIteration.lean`

```lean
import ClassificationFlagDifference

set_option linter.unusedSimpArgs false
namespace Classification349778

theorem iterDifference_smul (N j : ℕ) (c : ℝ) (v : Vec (N+j)) :
    iterDifference N j (c • v) = c • iterDifference N j v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change iterDifference N j (difference (N+j) (c • v)) = _
    rw [difference_smul, ih]
    rfl

theorem iterDifference_reversal (N j : ℕ) (v : Vec (N+j)) :
    iterDifference N j ((reversal (N+j)).mulVec v) =
      (-1 : ℝ)^j • (reversal N).mulVec (iterDifference N j v) := by
  induction j with
  | zero => simp [iterDifference]
  | succ j ih =>
    change iterDifference N j (difference (N+j) ((reversal (N+j+1)).mulVec v)) = _
    rw [difference_reversal]
    rw [← neg_one_smul ℝ ((reversal (N+j)).mulVec (difference (N+j) v)),
      iterDifference_smul, ih]
    simp only [smul_smul, pow_succ, iterDifference]
    congr 1
    ring

theorem iterDifference_transform (N j : ℕ) (a : Vec (N+j)) (v : Vec (N+j)) :
    iterDifference N j ((binomialTransform a).mulVec v) =
      (binomialTransform (fun i : Fin N => a ⟨i.val+j, by omega⟩)).mulVec
        (iterDifference N j v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change iterDifference N j (difference (N+j) ((binomialTransform a).mulVec v)) = _
    rw [difference_transform, ih]
    rfl

theorem iterDifference_intertwining (N j : ℕ) (a : Vec (N+j)) (v : Vec (N+j)) :
    iterDifference N j (((binomialTransform a) * reversal (N+j)).mulVec v) =
      (-1 : ℝ)^j •
        ((binomialTransform (fun i : Fin N => a ⟨i.val+j, by omega⟩)) * reversal N).mulVec
          (iterDifference N j v) := by
  rw [← Matrix.mulVec_mulVec, iterDifference_transform, iterDifference_reversal,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem flag_reversal_sized (N j : ℕ) (hN : 0 < N) (v : Vec (N+j))
    (hv : v ∈ flag (N+j) j) : (reversal (N+j)).mulVec v ∈ flag (N+j) j := by
  obtain ⟨c, hc⟩ := (flag_difference N j hN v).mp hv
  apply (flag_difference N j hN _).mpr
  refine ⟨(-1 : ℝ)^j * c, ?_⟩
  rw [iterDifference_reversal, hc]
  ext i
  simp [reversal_mulVec]

#print axioms iterDifference_intertwining
#print axioms flag_reversal_sized
end Classification349778
```

### `ClassificationSubdiagonal.lean`

```lean
import ClassificationTransform

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

theorem transform_subdiag {n : ℕ} (a : Vec (n+1)) (i : Fin n) :
    binomialTransform a i.succ i.castSucc =
      (i.val+1 : ℝ) * (a i.castSucc - a i.succ) := by
  classical
  rw [transform_entry]
  have hne : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  have hp : (-1 : ℝ)^(i.val+i.val) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  have hp' : (-1 : ℝ)^(i.val+1+i.val) = -1 := by
    rw [show i.val+1+i.val = (i.val+i.val)+1 by omega, pow_succ, hp]; ring
  calc
    _ = ∑ k ∈ ({i.castSucc, i.succ} : Finset (Fin (n+1))),
        (Nat.choose i.succ.val k.val : ℝ) * a k *
          ((-1 : ℝ)^(k.val+i.castSucc.val) * (Nat.choose k.val i.castSucc.val : ℝ)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp only [mem_insert, mem_singleton, not_or] at hk
      by_cases hki : k.val < i.val
      · simp [Nat.choose_eq_zero_of_lt hki]
      · have hik : i.val+1 < k.val := by
          have h₀ : k.val ≠ i.val := by intro h; exact hk.1 (Fin.ext h)
          have h₁ : k.val ≠ i.val+1 := by intro h; exact hk.2 (Fin.ext h)
          omega
        simp [Nat.choose_eq_zero_of_lt hik]
    _ = _ := by
      simp [hne, Fin.val_succ, Fin.val_castSucc, Nat.choose_succ_self_right, hp, hp']
      ring

theorem transform_parameters_antitone {n : ℕ} (a : Vec (n+1))
    (hn : ∀ i j, 0 ≤ binomialTransform a i j) (i : Fin n) :
    a i.succ ≤ a i.castSucc := by
  have h := hn i.succ i.castSucc
  rw [transform_subdiag] at h
  have hp : (0 : ℝ) < i.val+1 := by positivity
  nlinarith

#print axioms transform_subdiag
end Classification349778
```

### `ClassificationMaximum.lean`

```lean
import ClassificationDefinitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

/-- Equality in the finite weighted maximum bound propagates along every positive edge. -/
theorem maximum_propagation {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (a M : ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = a)
    (hu : ∀ k, |u k| ≤ M) (he : |∑ k, w k * u k| = a*M)
    (t : ι) (ht : 0 < w t) : |u t| = M := by
  have hbound : |∑ k, w k * u k| ≤ ∑ k, w k * |u k| := by
    calc
      _ ≤ ∑ k, |w k * u k| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hw _)]
  have hdef : ∑ k, w k * (M - |u k|) ≤ 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
    linarith
  have hnonneg : ∀ k, 0 ≤ w k * (M - |u k|) :=
    fun k => mul_nonneg (hw k) (sub_nonneg.mpr (hu k))
  have htdef : w t * (M - |u t|) ≤ 0 :=
    le_trans (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ t)) hdef
  have : M - |u t| ≤ 0 := by nlinarith
  linarith [hu t]

/-- The graph argument uses only known rows, never the final row. -/
theorem known_row_zero_maximum (N : ℕ) (P : Mat (N+2)) (a : ℝ) (u : Vec (N+2))
    (ha : 0 < a)
    (hn : ∀ i j, i.val+1 < N+2 → 0 ≤ P i j)
    (hs : ∀ i, i.val+1 < N+2 → ∑ j, P i j = a)
    (hh : ∀ i, i.val+1 < N+2 → P.mulVec u i = a*u i)
    (hfirst : u 0 = 0) (hlast : u (Fin.last (N+1)) = 0)
    (hanti : ∀ i j, 0 < i.val → i.val+1 < N+2 → i.val+j.val+1 = N+2 →
      0 < P i j)
    (hsub : ∀ i j, 0 < i.val → i.val+1 < N+2 → i.val+j.val = N+2 →
      0 < P i j) : u = 0 := by
  classical
  obtain ⟨t, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |u i|)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (N+2))).Nonempty)
  have hM : ∀ k, |u k| ≤ |u t| := fun k => hmax k (mem_univ k)
  have hprop : ∀ i j, i.val+1 < N+2 → |u i| = |u t| →
      0 < P i j → |u j| = |u t| := by
    intro i j hi hui hij
    apply maximum_propagation (P i) u a |u t| (fun k => hn i k hi) (hs i hi) hM
      ?_ j hij
    change |P.mulVec u i| = _
    rw [hh i hi, abs_mul, abs_of_pos ha, hui]
  by_cases hzero : |u t| = 0
  · ext k
    have : |u k| = 0 := le_antisymm (by simpa [hzero] using hM k) (abs_nonneg _)
    simpa using (abs_eq_zero.mp this)
  have hpos : 0 < |u t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
  have hinterior : ∀ k, |u k| = |u t| → 0 < k.val ∧ k.val+1 < N+2 := by
    intro k hk
    constructor
    · by_contra h
      have : k = 0 := Fin.ext (Nat.eq_zero_of_not_pos h)
      subst k
      rw [hfirst, abs_zero] at hk
      linarith
    · by_contra h
      have : k = Fin.last (N+1) := Fin.ext (by simp; omega)
      subst k
      rw [hlast, abs_zero] at hk
      linarith
  have hreach : ∀ k : ℕ, ∀ i : Fin (N+2), i.val = k → |u i| = |u t| →
      ∃ j : Fin (N+2), j.val = 1 ∧ |u j| = |u t| := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik him
      obtain ⟨hi0, hiN⟩ := hinterior i him
      by_cases hi1 : i.val = 1
      · exact ⟨i, hi1, him⟩
      have hi2 : 2 ≤ i.val := by omega
      let mid : Fin (N+2) := ⟨N+2-i.val, by omega⟩
      have hmid : |u mid| = |u t| :=
        hprop i mid hiN him (hsub i mid hi0 hiN (by dsimp [mid]; omega))
      obtain ⟨hm0, hmN⟩ := hinterior mid hmid
      let prev : Fin (N+2) := ⟨i.val-1, by omega⟩
      have hprev : |u prev| = |u t| :=
        hprop mid prev hmN hmid
          (hanti mid prev hm0 hmN (by dsimp [mid, prev]; omega))
      exact ih (i.val-1) (by omega) prev rfl hprev
  obtain ⟨one, hone, honeM⟩ := hreach t.val t rfl rfl
  obtain ⟨ho0, hoN⟩ := hinterior one honeM
  have hleak : 0 < P one (Fin.last (N+1)) :=
    hsub one (Fin.last (N+1)) ho0 hoN (by simp; omega)
  have := hprop one (Fin.last (N+1)) hoN honeM hleak
  rw [hlast, abs_zero] at this
  linarith

/-- Source maximum principle in terms of the actual transition matrix P = HJ.
The two edge assumptions are exactly its positive anti- and sub-antidiagonal entries. -/
theorem known_row_maximum_principle (N : ℕ) (P : Mat (N+2)) (a : ℝ)
    (u : Vec (N+2)) (ha : 0 < a)
    (hn : ∀ i j, i.val+1 < N+2 → 0 ≤ P i j)
    (hs : ∀ i, i.val+1 < N+2 → ∑ j, P i j = a)
    (hh : ∀ i, i.val+1 < N+2 → P.mulVec u i = a*u i)
    (hrow0 : ∀ j, P 0 j = if j = Fin.last (N+1) then a else 0)
    (hanti : ∀ i j, 0 < i.val → i.val+1 < N+2 → i.val+j.val+1 = N+2 →
      0 < P i j)
    (hsub : ∀ i j, 0 < i.val → i.val+1 < N+2 → i.val+j.val = N+2 →
      0 < P i j) : ∃ c, u = fun _ => c := by
  classical
  have hend : u (Fin.last (N+1)) = u 0 := by
    have h := hh 0 (by simp)
    simp only [Matrix.mulVec, dotProduct, hrow0] at h
    simp at h
    exact h.resolve_right (ne_of_gt ha)
  let v : Vec (N+2) := fun i => u i-u 0
  have hv : v = 0 := by
    apply known_row_zero_maximum N P a v ha hn hs ?_ ?_ ?_ hanti hsub
    · intro i hi
      change (∑ j, P i j * (u j-u 0)) = _
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs i hi]
      change P.mulVec u i - a*u 0 = _
      rw [hh i hi]
      dsimp [v]
      ring
    · simp [v]
    · simp [v, hend]
  refine ⟨u 0, ?_⟩
  funext i
  have := congrFun hv i
  dsimp [v] at this
  simpa only [sub_eq_zero] using this

#print axioms maximum_propagation
#print axioms known_row_maximum_principle
end Classification349778
```

### `ClassificationTransformMaximum.lean`

```lean
import ClassificationSubdiagonal
import ClassificationMaximum

set_option linter.unusedSimpArgs false
namespace Classification349778

lemma mul_reversal_entry {n : ℕ} (A : Mat n) (i j : Fin n) :
    (A * reversal n) i j = A i j.rev := by
  classical
  simp [Matrix.mul_apply, reversal, mul_ite]

lemma transform_row_zero {n : ℕ} (a : Vec (n+1)) (j : Fin (n+1)) :
    binomialTransform a 0 j = if j = 0 then a 0 else 0 := by
  classical
  by_cases hj : j = 0
  · subst j; simp [transform_diag]
  · rw [ite_eq_right hj]
    exact transform_lower a 0 j (by change 0 < j.val; exact Nat.pos_of_ne_zero (by
      intro h; exact hj (Fin.ext h)))

/-- The proof's maximum principle, with no hypothesis on the unknown final row. -/
theorem transform_maximum_principle (N : ℕ) (a : Vec (N+2)) (u : Vec (N+2))
    (hp : ∀ i : Fin (N+2), i.val+1 < N+2 → 0 < a i)
    (hd : ∀ i j : Fin (N+2), i < j → j.val+1 < N+2 → a j < a i)
    (hn : ∀ i j, i.val+1 < N+2 → 0 ≤ binomialTransform a i j)
    (hh : KnownRowsHarmonic (binomialTransform a) (a 0) u) :
    ∃ c, u = fun _ => c := by
  classical
  apply known_row_maximum_principle N (binomialTransform a * reversal (N+2))
    (a 0) u (hp 0 (by simp))
  · intro i j hi
    rw [mul_reversal_entry]
    exact hn i j.rev hi
  · intro i _
    simp_rw [mul_reversal_entry]
    have hsum := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N+2)))
      (fun j => binomialTransform a i j)
    exact hsum.trans (transform_row_sum a i)
  · exact hh
  · intro j
    rw [mul_reversal_entry, transform_row_zero]
    have hj : j.rev = 0 ↔ j = Fin.last (N+1) := by
      constructor
      · intro h
        have h' := congrArg Fin.rev h
        simpa using h'
      · intro h
        subst j
        simp
    simp [hj]
  · intro i j _ hi hij
    rw [mul_reversal_entry]
    have hj : j.rev = i := by apply Fin.ext; simp only [Fin.val_rev]; omega
    rw [hj, transform_diag]
    exact hp i hi
  · intro i j hi0 hi hij
    rw [mul_reversal_entry]
    let k : Fin (N+1) := ⟨i.val-1, by omega⟩
    have hi' : i = k.succ := by apply Fin.ext; dsimp [k]; omega
    have hj : j.rev = k.castSucc := by apply Fin.ext; simp [Fin.rev]; dsimp [k]; omega
    rw [hi', hj, transform_subdiag]
    have hdec : a k.succ < a k.castSucc := hd _ _ (by simp) (by rw [← hi']; exact hi)
    exact mul_pos (by positivity) (sub_pos.mpr hdec)

#print axioms transform_maximum_principle
end Classification349778
```

### `ClassificationSpectrum.lean`

```lean
import ClassificationDefinitions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

lemma roots_indexed_product {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
  classical
  have h := roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using h

/-- Literal eigenvalues with multiplicities are equivalent to the full polynomial identity.
No diagonalizability is imposed on the matrix whose spectrum is listed. -/
theorem spectrum_iff_charpoly {n : ℕ} (A : Mat n) (a : Vec n) :
    HasRealSpectrum A a ↔ A.charpoly = ∏ i, (X-C (a i)) := by
  classical
  constructor
  · intro h
    have hc : ((A.map Complex.ofRealHom).charpoly.roots).card =
        (A.map Complex.ofRealHom).charpoly.natDegree := by
      rw [h]
      simp [Matrix.charpoly_natDegree_eq_dim]
    have he := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (Matrix.charpoly_monic (A.map Complex.ofRealHom)) hc
    rw [h, Multiset.map_map, Function.comp_def, Finset.prod_map_val] at he
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    rw [← Matrix.charpoly_map]
    simpa [Polynomial.map_prod, Polynomial.map_sub] using he.symm
  · intro h
    unfold HasRealSpectrum
    rw [Matrix.charpoly_map, h]
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Complex.ofRealHom_eq_coe]
    exact roots_indexed_product _

#print axioms spectrum_iff_charpoly
end Classification349778
```

### `ClassificationLeading.lean`

```lean
import ClassificationTransform

set_option linter.unusedSimpArgs false
namespace Classification349778

lemma sum_leading_eq {n m : ℕ} (h : m ≤ n) (f : Fin n → ℝ)
    (hz : ∀ i, m ≤ i.val → f i = 0) :
    ∑ i : Fin m, f (Fin.castLE h i) = ∑ i : Fin n, f i := by
  classical
  apply Finset.sum_bij_ne_zero (fun i _ _ => Fin.castLE h i)
  · simp
  · intro i _ _ j _ _ hij
    exact Fin.castLE_injective _ hij
  · intro j _ hj
    have hjm : j.val < m := by
      by_contra hjm
      exact hj (hz j (by omega))
    exact ⟨⟨j.val, hjm⟩, Finset.mem_univ _, hj, rfl⟩
  · intros; rfl

lemma leading_lower {n m : ℕ} (A : Mat n) (h : m ≤ n) (hA : LowerTriangular A) :
    LowerTriangular (leading A m h) := by
  intro i j hij
  exact hA _ _ hij

lemma leading_leading {n m k : ℕ} (A : Mat n) (h : m ≤ n) (hk : k ≤ m) :
    leading (leading A m h) k hk = leading A k (hk.trans h) := rfl

lemma leading_mul {n m : ℕ} (A B : Mat n) (h : m ≤ n) (hA : LowerTriangular A) :
    leading (A*B) m h = leading A m h * leading B m h := by
  ext i j
  change (∑ k : Fin n, A (Fin.castLE h i) k * B k (Fin.castLE h j)) =
    ∑ k : Fin m, A (Fin.castLE h i) (Fin.castLE h k) *
      B (Fin.castLE h k) (Fin.castLE h j)
  symm
  apply sum_leading_eq h (fun k => A (Fin.castLE h i) k * B k (Fin.castLE h j))
  intro k hk
  rw [hA _ _ (by change i.val < k.val; omega), zero_mul]

lemma leading_pascal {n m : ℕ} (h : m ≤ n) : leading (pascal n) m h = pascal m := rfl
lemma leading_pascalInv {n m : ℕ} (h : m ≤ n) :
    leading (pascalInv n) m h = pascalInv m := rfl

lemma leading_diagonal {n m : ℕ} (a : Vec n) (h : m ≤ n) :
    leading (Matrix.diagonal a) m h = Matrix.diagonal (fun i => a (Fin.castLE h i)) := by
  classical
  ext i j
  simp [leading, Matrix.diagonal, Fin.castLE_injective h |>.eq_iff]

theorem leading_transform {n m : ℕ} (a : Vec n) (h : m ≤ n) :
    leading (binomialTransform a) m h =
      binomialTransform (fun i => a (Fin.castLE h i)) := by
  have hd : LowerTriangular (Matrix.diagonal a) := by
    intro i j hij; simp [Matrix.diagonal, ne_of_lt hij]
  rw [binomialTransform, pascal_inv,
    leading_mul _ _ h (lower_mul (pascal_lower n) hd),
    leading_mul _ _ h (pascal_lower n), leading_pascal, leading_diagonal, leading_pascalInv]
  rw [binomialTransform, pascal_inv]

theorem leading_stochastic {n m : ℕ} (A : Mat n) (h : m ≤ n)
    (hA : LowerTriangular A) (hs : Stochastic A) : Stochastic (leading A m h) := by
  constructor
  · intro i j; exact hs.1 _ _
  · intro i
    change ∑ j : Fin m, A (Fin.castLE h i) (Fin.castLE h j) = 1
    calc
      _ = ∑ j : Fin n, A (Fin.castLE h i) j := by
        apply sum_leading_eq h (fun j => A (Fin.castLE h i) j)
        intro j hj
        exact hA _ _ (by change i.val < j.val; omega)
      _ = 1 := hs.2 _

theorem leading_distinct {n m : ℕ} (A : Mat n) (h : m ≤ n)
    (hi : Function.Injective (fun i => A i i)) :
    Function.Injective (fun i => leading A m h i i) := by
  intro i j hij
  exact Fin.castLE_injective _ (hi hij)

theorem leading_global {n m : ℕ} (A : Mat n) (h : m ≤ n)
    (hA : GlobalAntiDiagonalCharpoly A) : GlobalAntiDiagonalCharpoly (leading A m h) := by
  intro k hk
  rw [leading_leading]
  exact hA k (hk.trans h)

#print axioms leading_transform
#print axioms leading_stochastic
#print axioms leading_global
end Classification349778
```

### `ClassificationEntryFormula.lean`

```lean
import ClassificationTransform

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

noncomputable def extend {n : ℕ} (a : Vec n) (k : ℕ) : ℝ :=
  if h : k < n then a ⟨k,h⟩ else 0

@[simp] lemma extend_val {n : ℕ} (a : Vec n) (k : Fin n) : extend a k.val = a k := by
  simp [extend, k.isLt]

/-- Source Lemma 2.2(iv), including the zero entries above the diagonal. -/
theorem transform_difference_entry {n : ℕ} (a : Vec n) (i j : Fin n) :
    binomialTransform a i j = (Nat.choose i.val j.val : ℝ) *
      ∑ k ∈ range (i.val-j.val+1), (-1 : ℝ)^k *
        (Nat.choose (i.val-j.val) k : ℝ) * extend a (j.val+k) := by
  classical
  by_cases hji : j.val ≤ i.val
  · rw [transform_entry]
    have hreindex : (∑ k : Fin n, (Nat.choose i.val k.val : ℝ) * a k *
        ((-1 : ℝ)^(k.val+j.val) * (Nat.choose k.val j.val : ℝ))) =
        ∑ t ∈ range (i.val-j.val+1), (Nat.choose i.val (j.val+t) : ℝ) *
          extend a (j.val+t) *
          ((-1 : ℝ)^(j.val+t+j.val) * (Nat.choose (j.val+t) j.val : ℝ)) := by
      symm
      apply Finset.sum_bij_ne_zero (fun t ht _ =>
        (⟨j.val+t, by have := mem_range.mp ht; omega⟩ : Fin n))
      · simp
      · intro t _ _ s _ _ heq; have := congrArg Fin.val heq; simp at this; omega
      · intro k _ hk0
        have hk1 : j.val ≤ k.val := by
          by_contra h
          simp [Nat.choose_eq_zero_of_lt (show k.val<j.val by omega)] at hk0
        have hk2 : k.val ≤ i.val := by
          by_contra h
          simp [Nat.choose_eq_zero_of_lt (show i.val<k.val by omega)] at hk0
        refine ⟨k.val-j.val, by simp only [mem_range]; omega, ?_, ?_⟩
        · simpa [show j.val+(k.val-j.val)=k.val by omega] using hk0
        · apply Fin.ext; simp; omega
      · intro t ht _
        have htn : j.val+t < n := by have := mem_range.mp ht; omega
        simp [extend, htn]
    rw [hreindex, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hc : (Nat.choose i.val (j.val+t) : ℝ) * (Nat.choose (j.val+t) j.val : ℝ) =
        (Nat.choose i.val j.val : ℝ) * (Nat.choose (i.val-j.val) t : ℝ) := by
      exact_mod_cast (by simpa using (Nat.choose_mul (n := i.val) (k := j.val+t)
        (s := j.val) (by omega)))
    have hp : (-1 : ℝ)^(j.val+t+j.val) = (-1 : ℝ)^t := by
      rw [show j.val+t+j.val = 2*j.val+t by omega, pow_add, pow_mul]
      norm_num
    rw [hp]
    calc
      _ = ((Nat.choose i.val (j.val+t) : ℝ) * (Nat.choose (j.val+t) j.val : ℝ)) *
          ((-1 : ℝ)^t * extend a (j.val+t)) := by ring
      _ = _ := by rw [hc]; ring
  · have hij : i < j := by change i.val < j.val; omega
    rw [transform_lower a i j hij, Nat.choose_eq_zero_of_lt hij, Nat.cast_zero, zero_mul]

#print axioms transform_difference_entry
end Classification349778
```

### `ClassificationShift.lean`

```lean
import ClassificationEntryFormula

set_option linter.unusedSimpArgs false
namespace Classification349778
open Finset

noncomputable def shift {N : ℕ} (s : ℕ) (a : Vec (N+s)) : Vec N :=
  fun i => a ⟨i.val+s, by omega⟩

/-- Division-free version of the proof's shifted-entry ratio (6). -/
theorem shifted_entry (N s : ℕ) (a : Vec (N+s)) (i k : Fin N) :
    (Nat.choose (i.val+s) (k.val+s) : ℝ) * binomialTransform (shift s a) i k =
      (Nat.choose i.val k.val : ℝ) *
        binomialTransform a ⟨i.val+s, by omega⟩ ⟨k.val+s, by omega⟩ := by
  classical
  by_cases hki : k.val ≤ i.val
  · have hs : (∑ t ∈ range (i.val-k.val+1), (-1 : ℝ)^t *
        (Nat.choose (i.val-k.val) t : ℝ) * extend (shift s a) (k.val+t)) =
        ∑ t ∈ range (i.val-k.val+1), (-1 : ℝ)^t *
          (Nat.choose (i.val-k.val) t : ℝ) * extend a (k.val+s+t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := mem_range.mp ht
      have h₁ : k.val+t < N := by omega
      have h₂ : k.val+s+t < N+s := by omega
      have he : extend (shift s a) (k.val+t) = extend a (k.val+s+t) := by
        simp only [extend, dite_eq_left h₁, dite_eq_left h₂, shift]
        congr 1
        apply Fin.ext
        simp; omega
      rw [he]
    simp only [transform_difference_entry, Nat.add_sub_add_right]
    rw [hs]
    ring
  · have hik : i < k := by change i.val < k.val; omega
    rw [transform_lower (shift s a) i k hik, mul_zero,
      Nat.choose_eq_zero_of_lt hik, Nat.cast_zero, zero_mul]

theorem shifted_known_nonneg (N s : ℕ) (a : Vec (N+s))
    (hn : ∀ i k, i.val+1 < N+s → 0 ≤ binomialTransform a i k) :
    ∀ i k : Fin N, i.val+1 < N → 0 ≤ binomialTransform (shift s a) i k := by
  intro i k hi
  by_cases hik : k ≤ i
  · have h := shifted_entry N s a i k
    have hc : (0 : ℝ) < Nat.choose (i.val+s) (k.val+s) := by
      exact_mod_cast (Nat.choose_pos (by omega))
    have hc' : (0 : ℝ) ≤ Nat.choose i.val k.val := Nat.cast_nonneg _
    have hh := hn ⟨i.val+s, by omega⟩ ⟨k.val+s, by omega⟩ (by simp; omega)
    have hprod := mul_nonneg hc' hh
    nlinarith
  · rw [transform_lower (shift s a) i k (lt_of_not_ge hik)]

#print axioms shifted_entry
#print axioms shifted_known_nonneg
end Classification349778
```

### `ClassificationFidelity.lean`

```lean
import ClassificationLeading
import ClassificationSpectrum

namespace Classification349778

/-- One direction needs no simple-spectrum hypothesis: the literal source condition
already includes every leading spectrum, with multiplicity. -/
theorem global_implies_charpoly {n : ℕ} (A : Mat n)
    (h : GlobalAntiDiagonalEigenvalue A) : GlobalAntiDiagonalCharpoly A := by
  intro m hm
  exact (spectrum_iff_charpoly _ _).mp (h.2 m hm).2.2

/-- The only additional obligation for the reverse fidelity bridge is precisely
real diagonalizability of every leading block of L, as required by the source. -/
theorem global_fidelity_of_diagonalizable {n : ℕ} (A : Mat n)
    (hl : LowerTriangular A)
    (hd : ∀ m (hm : m ≤ n), Diagonalizable (leading A m hm)) :
    GlobalAntiDiagonalEigenvalue A ↔ GlobalAntiDiagonalCharpoly A := by
  constructor
  · exact global_implies_charpoly A
  · intro h
    refine ⟨hl, fun m hm => ⟨leading_lower A hm hl, hd m hm, ?_⟩⟩
    exact (spectrum_iff_charpoly _ _).mpr (h m hm)

theorem transform_global_fidelity {n : ℕ} (a : Vec n) :
    GlobalAntiDiagonalEigenvalue (binomialTransform a) ↔
      GlobalAntiDiagonalCharpoly (binomialTransform a) := by
  apply global_fidelity_of_diagonalizable _ (transform_lower a)
  intro m hm
  rw [leading_transform]
  exact transform_diagonalizable _

#print axioms global_implies_charpoly
#print axioms global_fidelity_of_diagonalizable
#print axioms transform_global_fidelity
end Classification349778
```

### `ClassificationEigenvector.lean`

```lean
import ClassificationIteration
import ClassificationShift
import ClassificationTransformMaximum

set_option linter.unusedSimpArgs false
namespace Classification349778

theorem iterDifference_sub (N j : ℕ) (u v : Vec (N+j)) :
    iterDifference N j (u-v) = iterDifference N j u - iterDifference N j v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change iterDifference N j (differenceLin (N+j) (u-v)) = _
    rw [map_sub, ih]
    rfl

/-- The shifted-row argument in the induction: old eigenvectors lie in the binomial flag.
No nonzero assumption on v or on its finite difference is needed. -/
theorem eigenvector_in_flag (N j : ℕ) (a : Vec (N+2+j)) (L : Mat (N+2+j))
    (v : Vec (N+2+j))
    (hrows : ∀ i k, i.val+1 < N+2+j → L i k = binomialTransform a i k)
    (hn : ∀ i k, i.val+1 < N+2+j → 0 ≤ L i k)
    (hp : ∀ i : Fin (N+2+j), i.val+1 < N+2+j → 0 < a i)
    (hd : ∀ i k : Fin (N+2+j), i < k → k.val+1 < N+2+j → a k < a i)
    (he : (L * reversal (N+2+j)).mulVec v =
      ((-1 : ℝ)^j * a ⟨j, by omega⟩) • v) :
    v ∈ flag (N+2+j) j := by
  let u := iterDifference (N+2) j v
  have hHnonneg : ∀ i k, i.val+1 < N+2+j → 0 ≤ binomialTransform a i k := by
    intro i k hi; rw [← hrows i k hi]; exact hn i k hi
  have hsupp : ∀ i : Fin (N+2+j), i.val+1 < N+2+j →
      ((L * reversal (N+2+j)).mulVec v -
        ((binomialTransform a) * reversal (N+2+j)).mulVec v) i = 0 := by
    intro i hi
    apply sub_eq_zero.mpr
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_reversal_entry, mul_reversal_entry, hrows i k.rev hi]
  have hD := iterDifference_last_support (N+2) j _ hsupp
  rw [iterDifference_sub, he, iterDifference_smul, iterDifference_intertwining] at hD
  have hsign : (-1 : ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hh : KnownRowsHarmonic (binomialTransform (shift j a)) ((shift j a) 0) u := by
    intro i hi
    have hz := hD i hi
    change ((-1 : ℝ)^j * a ⟨j, by omega⟩) * u i -
      (-1 : ℝ)^j * ((binomialTransform (shift j a) * reversal (N+2)).mulVec u i) = 0 at hz
    have hz' : (-1 : ℝ)^j *
        (a ⟨j, by omega⟩ * u i -
          (binomialTransform (shift j a) * reversal (N+2)).mulVec u i) = 0 := by
      nlinarith [hz]
    have hval := (mul_eq_zero.mp hz').resolve_left hsign
    have h0 : (shift j a) 0 = a ⟨j, by omega⟩ := by simp [shift]
    rw [h0]
    exact (sub_eq_zero.mp hval).symm
  obtain ⟨c, hc⟩ := transform_maximum_principle N (shift j a) u
    (by intro i hi; exact hp ⟨i.val+j, by omega⟩ (by simp; omega))
    (by
      intro i k hik hk
      exact hd ⟨i.val+j, by omega⟩ ⟨k.val+j, by omega⟩
        (by change i.val+j < k.val+j; omega) (by simp; omega))
    (shifted_known_nonneg (N+2) j a hHnonneg) hh
  exact (flag_difference (N+2) j (by omega) v).mpr ⟨c, hc⟩

#print axioms eigenvector_in_flag
end Classification349778
```

### `ClassificationRigidity.lean`

```lean
import ClassificationIteration
import ClassificationTransformMaximum

set_option linter.unusedSimpArgs false
namespace Classification349778

/-- An exceptional last row with zero final coefficient is determined by its action
on the codimension-one flag. -/
theorem last_row_zero_of_annihilates_flag (n : ℕ) (E : Mat (n+2))
    (hd : E (Fin.last (n+1)) (Fin.last (n+1)) = 0)
    (hk : ∀ v, v ∈ flag (n+2) n → E.mulVec v = 0)
    (hr : ∀ i j, i.val+1 < n+2 → E i j = 0) : E = 0 := by
  classical
  have hall : ∀ v : Vec (n+2), E.mulVec v = 0 := by
    intro v
    obtain ⟨w, hw⟩ := (flag_restrict_bijective (n := n+2) (d := n) (by omega)).surjective
      (fun i : Fin (n+1) => v (Fin.castLE (show n+1 ≤ n+2 by omega) i))
    have heq : E.mulVec v = E.mulVec (w : Vec (n+2)) := by
      ext i
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val+1 < n+2
      · let j' : Fin (n+1) := ⟨j.val, by omega⟩
        have h : (w : Vec (n+2)) j = v j := congrFun hw j'
        rw [h]
      · have hjlast : j = Fin.last (n+1) := Fin.ext (by simp; omega)
        subst j
        by_cases hi : i.val+1 < n+2
        · rw [hr i _ hi, zero_mul, zero_mul]
        · have hilast : i = Fin.last (n+1) := Fin.ext (by simp; omega)
          subst i
          rw [hd, zero_mul, zero_mul]
    rw [heq]
    exact hk w w.property
  ext i j
  have h := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h

/-- The final rigidity argument of the written induction, separate from the
spectral argument that supplies invariance of L J. -/
theorem last_row_rigidity (n : ℕ) (a : Vec (n+2)) (L : Mat (n+2))
    (hrows : ∀ i k, i.val+1 < n+2 → L i k = binomialTransform a i k)
    (hdiag : L (Fin.last (n+1)) (Fin.last (n+1)) = a (Fin.last (n+1)))
    (hinv : ∀ v, v ∈ flag (n+2) n →
      (L * reversal (n+2)).mulVec v ∈ flag (n+2) n) :
    L = binomialTransform a := by
  let E := L - binomialTransform a
  have hkillJ : ∀ v, v ∈ flag (n+2) n →
      (E * reversal (n+2)).mulVec v = 0 := by
    intro v hv
    have hJ : (reversal (n+2)).mulVec v ∈ flag (n+2) n := by
      have h := flag_reversal_sized 2 n (by omega)
      have he : 2+n = n+2 := by omega
      rw [he] at h
      exact h v hv
    have hH : ((binomialTransform a) * reversal (n+2)).mulVec v ∈ flag (n+2) n := by
      rw [← Matrix.mulVec_mulVec]
      exact flag_transform (by omega) a _ hJ
    have hmem : (E * reversal (n+2)).mulVec v ∈ flag (n+2) n := by
      dsimp [E]
      rw [Matrix.sub_mul, Matrix.sub_mulVec]
      exact Submodule.sub_mem _ (hinv v hv) hH
    apply flag_zero_of_leading_zero (show n+1 ≤ n+2 by omega) _ hmem
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    rw [mul_reversal_entry]
    have h := hrows (Fin.castLE (show n+1 ≤ n+2 by omega) i) k.rev (by simp; omega)
    simp [E, h]
  have hkill : ∀ v, v ∈ flag (n+2) n → E.mulVec v = 0 := by
    intro v hv
    have hJ : (reversal (n+2)).mulVec v ∈ flag (n+2) n := by
      have h := flag_reversal_sized 2 n (by omega)
      have he : 2+n = n+2 := by omega
      rw [he] at h
      exact h v hv
    have h := hkillJ _ hJ
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, reversal_sq, Matrix.mul_one] at h
    exact h
  have hz : E = 0 := by
    apply last_row_zero_of_annihilates_flag n E
    · simp [E, hdiag, transform_diag]
    · exact hkill
    · intro i k hi; simp [E, hrows i k hi]
  exact sub_eq_zero.mp hz

#print axioms last_row_zero_of_annihilates_flag
#print axioms last_row_rigidity
end Classification349778
```

### `ClassificationSpectralSpan.lean`

```lean
import ClassificationFlag
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.unusedSimpArgs false
namespace Classification349778

theorem signed_old_injective {n : ℕ} (a : Vec n)
    (hp : ∀ i, 0 < a i) (hd : Function.Injective a) :
    Function.Injective (fun i => (-1 : ℝ)^i.val * a i) := by
  intro i j h
  apply hd
  have hh := congrArg abs h
  simpa [abs_mul, abs_pow, abs_of_pos (hp i), abs_of_pos (hp j)] using hh

theorem eigenvectors_span_flag (n : ℕ) (P : Mat (n+2))
    (t : Vec (n+1)) (v : Fin (n+1) → Vec (n+2))
    (ht : Function.Injective t) (hv : ∀ i, v i ≠ 0)
    (he : ∀ i, P.mulVec (v i) = t i • v i)
    (hf : ∀ i, v i ∈ flag (n+2) n) :
    Submodule.span ℝ (Set.range v) = flag (n+2) n := by
  have hli : LinearIndependent ℝ v := by
    apply Module.End.eigenvectors_linearIndependent' P.mulVecLin t ht v
    intro i
    exact ⟨Module.End.mem_eigenspace_iff.mpr (he i), hv i⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hf i
  · rw [finrank_span_eq_card hli, flag_finrank (by omega)]
    simp

#print axioms signed_old_injective
#print axioms eigenvectors_span_flag
end Classification349778
```

### `ClassificationZeroMinor.lean`

```lean
import ClassificationLeading
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.unusedSimpArgs false
namespace Classification349778

noncomputable def deletedPascalMinor {r : ℕ} (a : Vec (r+1)) (k : Fin (r+1)) : Mat r :=
  fun i j => binomialTransform a (k.succAbove i) j.castSucc
noncomputable def oldProduct {r : ℕ} (a : Vec (r+1)) : ℝ :=
  ∏ i : Fin r, a i.castSucc

lemma pascal_det (n : ℕ) : (pascal n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (pascal_lower n)]
  simp [pascal]

lemma pascalInv_det (n : ℕ) : (pascalInv n).det = 1 := by
  have h := congrArg Matrix.det (pascal_mul_pascalInv n)
  simpa [Matrix.det_mul, pascal_det] using h

lemma pascal_adjugate (n : ℕ) : (pascal n).adjugate = pascalInv n := by
  have h := Matrix.inv_def (pascal n)
  simpa [pascal_det, pascal_inv] using h.symm

lemma pascalInv_adjugate (n : ℕ) : (pascalInv n).adjugate = pascal n := by
  have h := Matrix.mul_adjugate (pascalInv n)
  rw [pascalInv_det, one_smul] at h
  calc
    _ = pascal n * (pascalInv n * (pascalInv n).adjugate) := by
      rw [← Matrix.mul_assoc, pascal_mul_pascalInv, Matrix.one_mul]
    _ = _ := by rw [h, Matrix.mul_one]

lemma transform_adjugate {n : ℕ} (a : Vec n) :
    (binomialTransform a).adjugate =
      pascal n * (Matrix.diagonal a).adjugate * pascalInv n := by
  rw [binomialTransform, pascal_inv, Matrix.adjugate_mul_distrib,
    Matrix.adjugate_mul_distrib, pascalInv_adjugate, pascal_adjugate, Matrix.mul_assoc]

lemma erase_last_product {r : ℕ} (a : Vec (r+1)) :
    (∏ i ∈ Finset.univ.erase (Fin.last r), a i) = oldProduct a := by
  classical
  unfold oldProduct
  symm
  apply Finset.prod_bij (fun i _ => i.castSucc)
  · intro i _; simp
  · intro i _ j _ h; exact Fin.castSucc_injective _ h
  · intro j hj
    have hne : j ≠ Fin.last r := (Finset.mem_erase.mp hj).1
    refine ⟨⟨j.val, by have := j.isLt; have := Fin.ext_iff.not.mp hne; simp at this; omega⟩,
      Finset.mem_univ _, ?_⟩
    rfl
  · intros; rfl

lemma zero_tail_adjugate_diagonal {r : ℕ} (a : Vec (r+1))
    (hz : a (Fin.last r) = 0) :
    (Matrix.diagonal a).adjugate =
      Matrix.diagonal (fun i => if i = Fin.last r then oldProduct a else 0) := by
  classical
  rw [Matrix.adjugate_diagonal]
  congr 1
  funext i
  by_cases hi : i = Fin.last r
  · subst i; simp [erase_last_product]
  · rw [ite_eq_right hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ _⟩)
    exact hz

lemma zero_tail_adjugate_entry {r : ℕ} (a : Vec (r+1))
    (hz : a (Fin.last r) = 0) (k : Fin (r+1)) :
    (binomialTransform a).adjugate (Fin.last r) k =
      oldProduct a * ((-1 : ℝ)^(r+k.val) * (Nat.choose r k.val : ℝ)) := by
  classical
  rw [transform_adjugate, zero_tail_adjugate_diagonal a hz, Matrix.mul_apply,
    Finset.sum_eq_single (Fin.last r)]
  · simp [Matrix.mul_diagonal, pascal, pascalInv]
  · intro j _ hj; simp [Matrix.mul_diagonal, hj]
  · simp

/-- The maximal-minor identity needs neither positivity nor a rank hypothesis. -/
theorem zero_tail_maximal_minor (r : ℕ) (a : Vec (r+1))
    (hz : a (Fin.last r) = 0) (k : Fin (r+1)) :
    (deletedPascalMinor a k).det = (Nat.choose r k.val : ℝ) * oldProduct a := by
  have h := zero_tail_adjugate_entry a hz k
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have hm : (binomialTransform a).submatrix k.succAbove (Fin.last r).succAbove =
      deletedPascalMinor a k := by
    ext i j; simp [deletedPascalMinor]
  rw [hm] at h
  have hs : (-1 : ℝ)^(k.val+r) = (-1 : ℝ)^(r+k.val) := by rw [Nat.add_comm]
  simp only [Fin.val_last] at h
  rw [hs] at h
  have hn : (-1 : ℝ)^(r+k.val) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hn
  calc
    _ = oldProduct a * ((-1 : ℝ)^(r+k.val) * (Nat.choose r k.val : ℝ)) := h
    _ = _ := by ring

#print axioms zero_tail_maximal_minor
end Classification349778
```

### `ClassificationReversalQuotient.lean`

```lean
import ClassificationIteration

set_option linter.unusedSimpArgs false
namespace Classification349778

/-- Reflection has the expected signed action on every binomial degree quotient. -/
theorem reversal_binomial_residual (n d : ℕ) :
    (reversal n).mulVec (binomialVector n d) -
      (-1 : ℝ)^d • binomialVector n d ∈
      Submodule.span ℝ (Set.range (fun k : Fin d => binomialVector n k.val)) := by
  induction d generalizing n with
  | zero =>
    have he : (reversal n).mulVec (binomialVector n 0) = binomialVector n 0 := by
      ext i; simp [reversal_mulVec, binomialVector]
    simp [he]
  | succ d ih =>
    cases n with
    | zero =>
      have he : (reversal 0).mulVec (binomialVector 0 (d+1)) -
          (-1 : ℝ)^(d+1) • binomialVector 0 (d+1) = 0 := by ext i; exact Fin.elim0 i
      rw [he]; exact Submodule.zero_mem _
    | succ n =>
      have he : difference n ((reversal (n+1)).mulVec (binomialVector (n+1) (d+1)) -
          (-1 : ℝ)^(d+1) • binomialVector (n+1) (d+1)) =
          -((reversal n).mulVec (binomialVector n d) -
            (-1 : ℝ)^d • binomialVector n d) := by
        change differenceLin n (_ - _) = _
        rw [map_sub]
        change difference n ((reversal (n+1)).mulVec _) - difference n (_ • _) = _
        rw [difference_reversal, difference_smul, difference_binomial_succ, pow_succ]
        ext i; simp; ring
      cases d with
      | zero =>
        change _ ∈ flag (n+1) 0
        apply (flag_zero_iff _).mpr
        apply (difference_eq_zero_iff n _).mp
        rw [he]
        have hz : (reversal n).mulVec (binomialVector n 0) = binomialVector n 0 := by
          ext i; simp [reversal_mulVec, binomialVector]
        simp [hz]
      | succ d =>
        change _ ∈ flag (n+1) (d+1)
        apply (flag_difference_step _).mpr
        rw [he]
        exact Submodule.neg_mem _ (ih n)

theorem flag_reversal_quotient {n : ℕ} (d : Fin n) :
    (reversal n).mulVec (binomialVector n d.val) -
      (-1 : ℝ)^d.val • binomialVector n d.val ∈
      Submodule.span ℝ (Set.range (fun k : Fin d.val => binomialVector n k.val)) :=
  reversal_binomial_residual n d.val

#print axioms flag_reversal_quotient
end Classification349778
```

### `ClassificationConverse.lean`

```lean
import ClassificationReversalQuotient
import ClassificationFidelity

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

lemma pascalInv_binomial {n : ℕ} (k : Fin n) :
    (pascalInv n).mulVec (binomialVector n k.val) = Pi.single k 1 := by
  have hb : binomialVector n k.val = (pascal n).mulVec (Pi.single k 1) := by
    ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, pascal, binomialVector]
  rw [hb, Matrix.mulVec_mulVec, pascalInv_mul_pascal, Matrix.one_mulVec]

lemma pascalInv_reflected_column {n : ℕ} (j : Fin n) :
    ∃ c : Fin j.val → ℝ,
      (pascalInv n).mulVec ((reversal n).mulVec (binomialVector n j.val)) =
        (-1 : ℝ)^j.val • Pi.single j 1 +
          ∑ k : Fin j.val, c k • Pi.single (⟨k.val, by omega⟩ : Fin n) 1 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (flag_reversal_quotient j)
  have h := congrArg (pascalInv n).mulVecLin hc
  rw [map_sum, map_sub, map_smul] at h
  simp only [map_smul, Matrix.coe_mulVecLin] at h
  have hk (k : Fin j.val) := pascalInv_binomial (⟨k.val, by omega⟩ : Fin n)
  simp_rw [hk] at h
  rw [pascalInv_binomial j] at h
  exact ⟨c, (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)⟩

lemma reversal_conjugate_upper (n : ℕ) :
    (pascalInv n * reversal n * pascal n).IsUpperTriangular := by
  classical
  intro i j hij
  change j.val < i.val at hij
  have he : (pascalInv n * reversal n * pascal n) i j =
      (pascalInv n).mulVec ((reversal n).mulVec (binomialVector n j.val)) i := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [he]
  obtain ⟨c, hc⟩ := pascalInv_reflected_column j
  rw [hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hne : i ≠ j := ne_of_gt hij
  rw [Pi.single_eq_of_ne hne, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro k _
  rw [Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega), mul_zero]

lemma reversal_conjugate_diag (n : ℕ) (j : Fin n) :
    (pascalInv n * reversal n * pascal n) j j = (-1 : ℝ)^j.val := by
  classical
  have he : (pascalInv n * reversal n * pascal n) j j =
      (pascalInv n).mulVec ((reversal n).mulVec (binomialVector n j.val)) j := by
    rw [Matrix.mulVec_mulVec]; rfl
  rw [he]
  obtain ⟨c, hc⟩ := pascalInv_reflected_column j
  rw [hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_eq_same, mul_one]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro k _
  rw [Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega), mul_zero]

/-- Source Proposition 2.3, proved by the signed quotient action in Pascal coordinates. -/
theorem transform_charpoly {n : ℕ} (a : Vec n) :
    ((binomialTransform a) * reversal n).charpoly = prescribedCharpoly (binomialTransform a) := by
  classical
  have hc : ((binomialTransform a) * reversal n).charpoly =
      (Matrix.diagonal a * (pascalInv n * reversal n * pascal n)).charpoly := by
    rw [binomialTransform, pascal_inv]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.charpoly_mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  rw [hc, Matrix.charpoly_of_isUpperTriangular]
  · unfold prescribedCharpoly signedDiagonal
    apply Finset.prod_congr rfl
    intro i _
    simp [Matrix.diagonal_mul, reversal_conjugate_diag, transform_diag, mul_comm]
  · intro i j hij
    simp [Matrix.diagonal_mul, reversal_conjugate_upper n hij]

theorem transform_global_charpoly {n : ℕ} (a : Vec n) :
    GlobalAntiDiagonalCharpoly (binomialTransform a) := by
  intro m hm
  rw [leading_transform]
  exact transform_charpoly _

theorem transform_global_eigenvalue {n : ℕ} (a : Vec n) :
    GlobalAntiDiagonalEigenvalue (binomialTransform a) :=
  (transform_global_fidelity a).mpr (transform_global_charpoly a)

#print axioms flag_reversal_quotient
#print axioms transform_global_charpoly
#print axioms transform_global_eigenvalue
end Classification349778
```

### `ClassificationSimpleSpectrum.lean`

```lean
import ClassificationFidelity
import ClassificationSpectralSpan
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

lemma lower_charpoly {n : ℕ} (A : Mat n) (hl : LowerTriangular A) :
    A.charpoly = ∏ i, (X - C (A i i)) := by
  rw [← Matrix.charpoly_transpose, Matrix.charpoly_of_isUpperTriangular]
  · rfl
  · intro i j hij; exact hl j i hij

lemma lower_complex_charpoly {n : ℕ} (A : Mat n) (hl : LowerTriangular A) :
    (A.map Complex.ofRealHom).charpoly = ∏ i, (X - C (A i i : ℂ)) := by
  rw [Matrix.charpoly_map, lower_charpoly A hl]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Complex.ofRealHom_eq_coe]

theorem lower_distinct_iff {n : ℕ} (A : Mat n) (hl : LowerTriangular A) :
    DistinctEigenvalues A ↔ Function.Injective (fun i => A i i) := by
  classical
  constructor
  · rintro ⟨a, ha, hc⟩
    have he := congrArg Polynomial.roots ((lower_complex_charpoly A hl).symm.trans hc)
    rw [roots_indexed_product, roots_indexed_product] at he
    have hn : (Finset.univ.val.map (fun i => (A i i : ℂ))).Nodup := by
      rw [he]
      exact Finset.univ.nodup.map ha
    intro i j hij
    have hmap : Function.Injective (fun i => (A i i : ℂ)) := by
      intro i j hij
      exact Multiset.inj_on_of_nodup_map hn i (by simp) j (by simp) hij
    exact hmap (congrArg (fun x : ℝ => (x : ℂ)) hij)
  · intro hd
    refine ⟨fun i => (A i i : ℂ), ?_, lower_complex_charpoly A hl⟩
    intro i j hij; apply hd; exact Complex.ofReal_injective hij

/-- Real roots of the characteristic polynomial supply real eigenvectors. -/
lemma eigenvector_of_charpoly {n : ℕ} (A : Mat n) (t : ℝ)
    (ht : A.charpoly.IsRoot t) :
    ∃ v : Vec n, v ≠ 0 ∧ A.mulVec v = t • v := by
  have he : Module.End.HasEigenvalue A.mulVecLin t := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  exact ⟨v, hv.2, Module.End.mem_eigenspace_iff.mp hv.1⟩

theorem lower_distinct_diagonalizable {n : ℕ} (A : Mat n) (hl : LowerTriangular A)
    (hd : Function.Injective (fun i => A i i)) : Diagonalizable A := by
  classical
  have he (i : Fin n) : ∃ v : Vec n, v ≠ 0 ∧ A.mulVec v = A i i • v := by
    apply eigenvector_of_charpoly
    rw [lower_charpoly A hl]
    simp only [Polynomial.IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  choose v hv heq using he
  have hli : LinearIndependent ℝ v := by
    apply Module.End.eigenvectors_linearIndependent' A.mulVecLin (fun i => A i i) hd v
    intro i
    exact ⟨Module.End.mem_eigenspace_iff.mpr (heq i), hv i⟩
  let Q : Mat n := fun i j => v j i
  have hQ : IsUnit Q.det := by
    apply (Matrix.isUnit_iff_isUnit_det Q).mp
    exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  refine ⟨Q, fun i => A i i, hQ, ?_⟩
  ext i j
  have h := congrFun (heq j) i
  change (A * Q) i j = (Q * Matrix.diagonal (fun i => A i i)) i j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, Q, mul_comm] using h

theorem global_fidelity {n : ℕ} (A : Mat n) (hl : LowerTriangular A)
    (hd : DistinctEigenvalues A) :
    GlobalAntiDiagonalEigenvalue A ↔ GlobalAntiDiagonalCharpoly A := by
  apply global_fidelity_of_diagonalizable A hl
  intro m hm
  exact lower_distinct_diagonalizable _ (leading_lower A hm hl)
    (leading_distinct A hm ((lower_distinct_iff A hl).mp hd))

#print axioms lower_distinct_diagonalizable
#print axioms global_fidelity
#print axioms lower_distinct_iff
#print axioms eigenvector_of_charpoly
end Classification349778
```

### `ClassificationParameterOrder.lean`

```lean
import ClassificationSubdiagonal
import Mathlib.Order.Fin.Basic

namespace Classification349778

theorem diagonal_strict_decreasing (n : ℕ) (a : Vec (n+1))
    (hn : ∀ i j, 0 ≤ binomialTransform a i j) (hd : Function.Injective a) :
    StrictAnti a := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  apply lt_of_le_of_ne (transform_parameters_antitone a hn i)
  intro he
  have hh := hd he
  have := congrArg Fin.val hh
  simp at this

#print axioms diagonal_strict_decreasing
end Classification349778
```

### `ClassificationPositiveStep.lean`

```lean
import ClassificationSimpleSpectrum
import ClassificationEigenvector
import ClassificationRigidity

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

lemma flag_mono {n d e : ℕ} (h : d ≤ e) : flag n d ≤ flag n e := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact flag_binomial (⟨i.val, by omega⟩ : Fin (e+1))

lemma eigenvector_in_flag_of_size (m N j : ℕ) (hm : m = N+2+j) (hj : j < m)
    (a : Vec m) (L : Mat m) (v : Vec m)
    (hrows : ∀ i k, i.val+1 < m → L i k = binomialTransform a i k)
    (hn : ∀ i k, i.val+1 < m → 0 ≤ L i k)
    (hp : ∀ i : Fin m, i.val+1 < m → 0 < a i)
    (hd : ∀ i k : Fin m, i < k → k.val+1 < m → a k < a i)
    (he : (L * reversal m).mulVec v = ((-1 : ℝ)^j * a ⟨j, hj⟩) • v) :
    v ∈ flag m j := by
  subst m
  exact eigenvector_in_flag N j a L v hrows hn hp hd he

/-- The complete spectral/rigidity induction step, with the old-zero case isolated
as the positivity obligation rather than silently assumed from distinctness. -/
theorem classification_step_positive (n : ℕ) (a : Vec (n+2)) (L : Mat (n+2))
    (hrows : ∀ i k, i.val+1 < n+2 → L i k = binomialTransform a i k)
    (hdiag : ∀ i, L i i = a i)
    (hn : ∀ i k, i.val+1 < n+2 → 0 ≤ L i k)
    (hp : ∀ i : Fin (n+2), i.val+1 < n+2 → 0 < a i)
    (hd : ∀ i k : Fin (n+2), i < k → k.val+1 < n+2 → a k < a i)
    (hc : (L * reversal (n+2)).charpoly = prescribedCharpoly L) :
    L = binomialTransform a := by
  classical
  let t : Vec (n+1) := fun j => (-1 : ℝ)^j.val * a j.castSucc
  have ht : Function.Injective t := by
    apply signed_old_injective (fun j => a j.castSucc)
    · intro j; exact hp _ (by simp; omega)
    · intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hij' | hji'
      · have hh := hd i.castSucc j.castSucc (by exact hij') (by simp; omega)
        exact (ne_of_lt hh) hij.symm
      · have hh := hd j.castSucc i.castSucc (by exact hji') (by simp; omega)
        exact (ne_of_lt hh) hij
  have hex (j : Fin (n+1)) : ∃ v : Vec (n+2), v ≠ 0 ∧
      (L * reversal (n+2)).mulVec v = t j • v := by
    apply eigenvector_of_charpoly
    rw [hc]
    unfold prescribedCharpoly
    simp only [Polynomial.IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero (Finset.mem_univ j.castSucc)
    simp [t, signedDiagonal, hdiag]
  choose v hv he using hex
  have hf (j : Fin (n+1)) : v j ∈ flag (n+2) n := by
    apply flag_mono (show j.val ≤ n by omega)
    exact eigenvector_in_flag_of_size (n+2) (n-j.val) j.val (by omega)
      (by omega) a L (v j) hrows hn hp hd (he j)
  have hspan := eigenvectors_span_flag n (L * reversal (n+2)) t v ht hv he hf
  apply last_row_rigidity n a L hrows (hdiag _)
  intro w hw
  rw [← hspan] at hw ⊢
  induction hw using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  | zero => simp
  | add u w _ _ hu hw =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hu

#print axioms classification_step_positive
end Classification349778
```

### `ClassificationInduction.lean`

```lean
import ClassificationPositiveStep
import ClassificationParameterOrder
import ClassificationConverse

set_option linter.unusedSimpArgs false
namespace Classification349778

/-- The zero-tail boundary proposition. This is a proposition, not an axiom.
ClassificationZeroBoundary proves it; the assembly below is parameterized by its proof. -/
def ZeroTailBoundary : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (a : Vec (r+1)),
    (∀ i : Fin r, 0 < a i.castSucc) → a (Fin.last r) = 0 →
    ∀ (L : Mat (r+2)), LowerTriangular L → Stochastic L →
    leading L (r+1) (by omega) = binomialTransform a →
    (L * reversal (r+2)).charpoly = prescribedCharpoly L →
    L (Fin.last (r+1)) (Fin.last (r+1)) = 0

/-- All induction and spectral assembly, parameterized by the
zero-tail boundary lemma. ClassificationEndpoint supplies its unconditional proof. -/
theorem classification_charpoly_forward_of_zero_tail (hz : ZeroTailBoundary)
    (n : ℕ) (A : Mat n) (hl : LowerTriangular A) (hs : Stochastic A)
    (hd : Function.Injective (fun i => A i i)) (hg : GlobalAntiDiagonalCharpoly A) :
    A = binomialTransform (fun i => A i i) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => ext i; exact Fin.elim0 i
    | succ n =>
      cases n with
      | zero =>
        ext i j
        have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
        subst i; subst j
        exact (transform_diag (fun i => A i i) 0).symm
      | succ n =>
        let b : Vec (n+1) := fun i => A i.castSucc i.castSucc
        let a : Vec (n+2) := fun i => A i i
        have hb : leading A (n+1) (by omega) = binomialTransform b := by
          exact ih (n+1) (by omega) _ (leading_lower A (by omega) hl)
            (leading_stochastic A (by omega) hl hs) (leading_distinct A (by omega) hd)
            (leading_global A (by omega) hg)
        have hbn : ∀ i j, 0 ≤ binomialTransform b i j := by
          rw [← hb]; intro i j; exact hs.1 _ _
        have hbd : Function.Injective b := leading_distinct A (by omega) hd
        have hanti : StrictAnti b := diagonal_strict_decreasing n b hbn hbd
        have hbnonneg (i : Fin (n+1)) : 0 ≤ b i := hs.1 _ _
        have hblast : 0 < b (Fin.last n) := by
          by_contra hpos
          have hbz : b (Fin.last n) = 0 := le_antisymm (le_of_not_gt hpos) (hbnonneg _)
          cases n with
          | zero =>
            have hst := (leading_stochastic A (by omega) hl hs).2 (0 : Fin 1)
            rw [hb] at hst
            rw [transform_row_sum] at hst
            have he : (Fin.last 0 : Fin 1) = 0 := rfl
            rw [he] at hbz
            linarith
          | succ n =>
            have hp (i : Fin (n+1)) : 0 < b i.castSucc := by
              rw [← hbz]
              exact hanti (by simp)
            have hnew := hz (n+1) (by omega) b hp hbz A hl hs hb
              (by simpa [leading] using hg (n+1+2) (by omega))
            have he : A (Fin.last (n+1)).castSucc (Fin.last (n+1)).castSucc =
                A (Fin.last (n+1+1)) (Fin.last (n+1+1)) := hbz.trans hnew.symm
            have hidx := hd he
            have hval := congrArg Fin.val hidx
            simp at hval
        have hp (i : Fin (n+2)) (hi : i.val+1 < n+2) : 0 < a i := by
          let k : Fin (n+1) := ⟨i.val, by omega⟩
          have he : a i = b k := rfl
          rw [he]
          exact lt_of_lt_of_le hblast (hanti.antitone (Fin.le_last k))
        have hrows : ∀ i k, i.val+1 < n+2 → A i k = binomialTransform a i k := by
          have hblocks : leading A (n+1) (by omega) =
              leading (binomialTransform a) (n+1) (by omega) := by
            rw [leading_transform]
            exact hb
          intro i k hi
          by_cases hk : k.val+1 < n+2
          · let i' : Fin (n+1) := ⟨i.val, by omega⟩
            let k' : Fin (n+1) := ⟨k.val, by omega⟩
            exact congrArg (fun M : Mat (n+1) => M i' k') hblocks
          · rw [hl i k (by change i.val < k.val; omega),
              transform_lower a i k (by change i.val < k.val; omega)]
        apply classification_step_positive n a A hrows (fun _ => rfl)
          (fun i k _ => hs.1 i k) hp
        · intro i k hik hk
          let i' : Fin (n+1) := ⟨i.val, by change i.val < k.val at hik; omega⟩
          let k' : Fin (n+1) := ⟨k.val, by omega⟩
          exact hanti (show i' < k' from hik)
        · simpa [leading] using hg (n+2) (by omega)

/-- Once the boundary lemma is supplied, the literal source endpoint follows.
ClassificationEndpoint discharges the explicit ZeroTailBoundary hypothesis. -/
theorem classification_iff_of_zero_tail (hz : ZeroTailBoundary)
    (n : ℕ) (A : Mat n) (hs : Stochastic A) (hd : DistinctEigenvalues A) :
    GlobalAntiDiagonalEigenvalue A ↔ ∃ a : Vec n, A = binomialTransform a := by
  constructor
  · intro hg
    exact ⟨fun i => A i i, classification_charpoly_forward_of_zero_tail hz n A hg.1 hs
      ((lower_distinct_iff A hg.1).mp hd) (global_implies_charpoly A hg)⟩
  · rintro ⟨a, rfl⟩
    exact transform_global_eigenvalue a

#print axioms classification_charpoly_forward_of_zero_tail
#print axioms classification_iff_of_zero_tail
end Classification349778
```

### `ClassificationZeroCoefficient.lean`

```lean
import ClassificationZeroMinor
import ClassificationTransformMaximum
import Mathlib.LinearAlgebra.Matrix.Polynomial

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

noncomputable def reversalPencil {n : ℕ} (H : Mat n) :
    Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
  fun i j => X * C (reversal n i j) - C (H i j)

lemma reversalPencil_det {n : ℕ} (H : Mat n) :
    (reversalPencil H).det = (H * reversal n).charpoly * C (reversal n).det := by
  have hm : reversalPencil H =
      (H * reversal n).charmatrix * (reversal n).map C := by
    rw [Matrix.charmatrix, Matrix.sub_mul]
    have hh : (H * reversal n).map C * (reversal n).map C = H.map C := by
      rw [← Matrix.map_mul, Matrix.mul_assoc H,
        reversal_sq, Matrix.mul_one]
    change reversalPencil H = Matrix.diagonal (fun _ => X) * (reversal n).map C -
      (H * reversal n).map C * (reversal n).map C
    rw [hh]
    ext i j
    simp [reversalPencil, Matrix.scalar, Matrix.diagonal_mul]
  rw [hm, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det C (reversal n)).symm

/-- The coefficient comparison in perturbation form. The last diagonal of e is zero.
No positivity hypothesis is needed. The sign is independent of the dimension. -/
theorem zero_tail_coefficient (r : ℕ) (a : Vec (r+1))
    (hz : a (Fin.last r) = 0) (H : Mat (r+2)) (hl : LowerTriangular H)
    (hb : leading H (r+1) (by omega) = binomialTransform a)
    (e : Vec (r+2)) (he : e (Fin.last (r+1)) = 0) :
    ((reversalPencil H).updateRow (Fin.last (r+1)) (fun j => C (e j))).det.coeff 1 =
      - e (Fin.last r).castSucc * oldProduct a := by
  classical
  let D := (reversalPencil H).updateRow (Fin.last (r+1)) (fun j => C (e j))
  have hcol (i : Fin (r+2)) : D i (Fin.last (r+1)) = if i = 0 then X else 0 := by
    by_cases hi : i = Fin.last (r+1)
    · subst i; simp [D, he]
    · have hil : i < Fin.last (r+1) := lt_of_le_of_ne (Fin.le_last i) hi
      have hir : reversal (r+2) i (Fin.last (r+1)) = if i = 0 then 1 else 0 := by
        simp [reversal]
      simp [D, Matrix.updateRow_apply, hi, reversalPencil, hl i _ hil, hir]
  have hdet : D.det = (-1 : Polynomial ℝ)^(r+1) * X *
      (D.submatrix Fin.succ Fin.castSucc).det := by
    rw [Matrix.det_succ_column D (Fin.last (r+1)), Finset.sum_eq_single 0]
    · simp [hcol]
    · intro i _ hi; rw [hcol, ite_eq_right hi]; simp
    · simp
  rw [show ((reversalPencil H).updateRow _ _).det = D.det from rfl, hdet]
  have hsign : (-1 : Polynomial ℝ)^(r+1) = C ((-1 : ℝ)^(r+1)) := by simp
  rw [hsign, mul_assoc, coeff_C_mul, coeff_X_mul]
  rw [coeff_zero_eq_eval_zero]
  let M : Mat (r+1) := fun i j => if i = Fin.last r then e j.castSucc
    else -H i.succ j.castSucc
  have hev : ((D.submatrix Fin.succ Fin.castSucc).map (evalRingHom 0)) = M := by
    ext i j
    by_cases hi : i = Fin.last r
    · subst i; simp [D, M, Matrix.updateRow_self]
    · have hi' : i.succ ≠ Fin.last (r+1) := by
        intro h; apply hi; apply Fin.ext; have := congrArg Fin.val h; simpa using this
      simp [D, M, Matrix.updateRow_apply, hi, hi', reversalPencil]
  change (-1 : ℝ)^(r+1) * (evalRingHom 0) _ = _
  rw [RingHom.map_det]
  change (-1 : ℝ)^(r+1) * ((D.submatrix Fin.succ Fin.castSucc).map (evalRingHom 0)).det = _
  rw [hev]
  have hmcol (i : Fin (r+1)) : M i (Fin.last r) =
      if i = Fin.last r then e (Fin.last r).castSucc else 0 := by
    by_cases hi : i = Fin.last r
    · simp [M, hi]
    · have hile : i.val+1 ≤ r := by
        have := i.isLt; have := Fin.ext_iff.not.mp hi; simp at this; omega
      let k : Fin (r+1) := ⟨i.val+1, by omega⟩
      have hh := congrArg (fun A : Mat (r+1) => A k (Fin.last r)) hb
      change H k.castSucc (Fin.last r).castSucc = binomialTransform a k (Fin.last r) at hh
      have hk : k.castSucc = i.succ := by apply Fin.ext; rfl
      rw [hk] at hh
      have ht : binomialTransform a k (Fin.last r) = 0 := by
        by_cases hkl : k = Fin.last r
        · rw [hkl, transform_diag, hz]
        · exact transform_lower a _ _ (lt_of_le_of_ne (Fin.le_last k) hkl)
      simp [M, hi, hh, ht]
  have hm : M.det = e (Fin.last r).castSucc *
      (-1 : ℝ)^r * oldProduct a := by
    rw [Matrix.det_succ_column M (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · have hminor : M.submatrix Fin.castSucc Fin.castSucc = -(deletedPascalMinor a 0) := by
        ext i j
        have hi : i.castSucc ≠ Fin.last r := Fin.castSucc_ne_last i
        have hh := congrArg (fun A : Mat (r+1) => A i.succ j.castSucc) hb
        change H i.succ.castSucc j.castSucc.castSucc = binomialTransform a i.succ j.castSucc at hh
        change (if i.castSucc = Fin.last r then e j.castSucc.castSucc
          else -H i.castSucc.succ j.castSucc.castSucc) =
            -binomialTransform a ((0 : Fin (r+1)).succAbove i) j.castSucc
        rw [ite_eq_right hi, Fin.succAbove_zero]
        exact congrArg Neg.neg hh
      simp only [Fin.val_last, hmcol, ite_true, Fin.succAbove_last, hminor,
        Matrix.det_neg, Fintype.card_fin, zero_tail_maximal_minor r a hz 0,
        Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      have hs : (-1 : ℝ)^(r+r) = 1 := by rw [← two_mul, pow_mul]; norm_num
      rw [hs]; ring
    · intro i _ hi; rw [hmcol, ite_eq_right hi]; simp
    · simp
  rw [hm, pow_succ]
  have hs : (-1 : ℝ)^r * (-1 : ℝ)^r = 1 := by rw [← pow_two, ← pow_mul]; norm_num
  calc
    _ = - (e (Fin.last r).castSucc * oldProduct a) *
        ((-1 : ℝ)^r * (-1 : ℝ)^r) := by ring
    _ = _ := by rw [hs]; ring

#print axioms zero_tail_coefficient
end Classification349778
```

### `ClassificationZeroBoundary.lean`

```lean
import ClassificationZeroCoefficient
import ClassificationInduction

set_option linter.unusedSimpArgs false
namespace Classification349778
open Polynomial

/-- Comparing L to the binomial transform with exactly its diagonal avoids
any assumption on the new last parameter. -/
theorem zero_tail_obstruction (r : ℕ) (_hr : 0 < r) (a : Vec (r+1))
    (hp : ∀ i : Fin r, 0 < a i.castSucc) (hz : a (Fin.last r) = 0)
    (L : Mat (r+2)) (hl : LowerTriangular L)
    (hb : leading L (r+1) (by omega) = binomialTransform a)
    (hc : (L * reversal (r+2)).charpoly = prescribedCharpoly L) :
    L (Fin.last (r+1)) (Fin.last r).castSucc =
      -(r+1 : ℝ) * L (Fin.last (r+1)) (Fin.last (r+1)) := by
  classical
  let b : Vec (r+2) := fun i => L i i
  let H := binomialTransform b
  have hparam : (fun i : Fin (r+1) => b i.castSucc) = a := by
    funext i
    have hh := congrArg (fun M : Mat (r+1) => M i i) hb
    change L i.castSucc i.castSucc = binomialTransform a i i at hh
    rw [transform_diag] at hh
    exact hh
  have hH : leading H (r+1) (by omega) = binomialTransform a := by
    dsimp only [H]
    rw [leading_transform]
    change binomialTransform (fun i => b i.castSucc) = _
    rw [hparam]
  have hrows (i j : Fin (r+2)) (hi : i ≠ Fin.last (r+1)) : L i j = H i j := by
    have hin : i.val < r+1 := by
      have := i.isLt; have := Fin.ext_iff.not.mp hi; simp at this; omega
    by_cases hj : j.val < r+1
    · let i' : Fin (r+1) := ⟨i.val, hin⟩
      let j' : Fin (r+1) := ⟨j.val, hj⟩
      have hh := congrArg (fun M : Mat (r+1) => M i' j') (hb.trans hH.symm)
      exact hh
    · change L i j = binomialTransform b i j
      rw [hl i j (by change i.val < j.val; omega),
        transform_lower b i j (by change i.val < j.val; omega)]
  have hchar : (L * reversal (r+2)).charpoly = (H * reversal (r+2)).charpoly := by
    rw [hc, transform_charpoly]
    unfold prescribedCharpoly signedDiagonal
    simp [H, transform_diag, b]
  have hdet : (reversalPencil L).det = (reversalPencil H).det := by
    rw [reversalPencil_det, reversalPencil_det, hchar]
  let e : Vec (r+2) := fun j => L (Fin.last (r+1)) j - H (Fin.last (r+1)) j
  have he : e (Fin.last (r+1)) = 0 := by simp [e, H, transform_diag, b]
  let D := (reversalPencil H).updateRow (Fin.last (r+1)) (fun j => C (e j))
  have hL : (reversalPencil H).updateRow (Fin.last (r+1))
      (reversalPencil L (Fin.last (r+1))) = reversalPencil L := by
    ext i j
    by_cases hi : i = Fin.last (r+1)
    · subst i; simp
    · simp [Matrix.updateRow_apply, hi, reversalPencil, hrows i j hi]
  have hsum : reversalPencil H (Fin.last (r+1)) =
      reversalPencil L (Fin.last (r+1)) + (fun j => C (e j)) := by
    funext j
    simp [reversalPencil, e]
  have hD : D.det = 0 := by
    have hh := Matrix.det_updateRow_add (reversalPencil H) (Fin.last (r+1))
      (reversalPencil L (Fin.last (r+1))) (fun j => C (e j))
    rw [← hsum, Matrix.updateRow_eq_self, hL, hdet] at hh
    exact (add_eq_left.mp hh.symm)
  have hcoef := zero_tail_coefficient r a hz H (transform_lower b) hH e he
  change D.det.coeff 1 = _ at hcoef
  rw [hD, coeff_zero] at hcoef
  have hprod : oldProduct a ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hp i))
  have her : e (Fin.last r).castSucc = 0 := by
    have hh : -e (Fin.last r).castSucc = 0 := (mul_eq_zero.mp hcoef.symm).resolve_right hprod
    exact neg_eq_zero.mp hh
  have hs := transform_subdiag b (Fin.last r)
  change H (Fin.last (r+1)) (Fin.last r).castSucc =
    (r+1 : ℝ) * (b (Fin.last r).castSucc - b (Fin.last (r+1))) at hs
  have hz' : b (Fin.last r).castSucc = 0 := by
    have hh := congrFun hparam (Fin.last r)
    exact hh.trans hz
  rw [hz'] at hs
  have heq := sub_eq_zero.mp her
  change L (Fin.last (r+1)) (Fin.last r).castSucc = H (Fin.last (r+1)) (Fin.last r).castSucc at heq
  rw [heq, hs]
  dsimp [b]
  ring

/-- Nonnegativity supplies the boundary consequence required by the induction. -/
theorem zero_tail_boundary : ZeroTailBoundary := by
  intro r hr a hp hz L hl hs hb hc
  have ho := zero_tail_obstruction r hr a hp hz L hl hb hc
  have hn := hs.1 (Fin.last (r+1)) (Fin.last r).castSucc
  have hz := hs.1 (Fin.last (r+1)) (Fin.last (r+1))
  have hr' : (0 : ℝ) < r+1 := by positivity
  nlinarith

#print axioms zero_tail_obstruction
#print axioms zero_tail_boundary
end Classification349778
```

### `ClassificationEndpoint.lean`

```lean
import ClassificationZeroBoundary
import ClassificationSanity

namespace Classification349778

/-- The unconditional forward classification with the exact diagonal parameters. -/
theorem classification_charpoly_forward (n : ℕ) (A : Mat n)
    (hl : LowerTriangular A) (hs : Stochastic A)
    (hd : Function.Injective (fun i => A i i)) (hg : GlobalAntiDiagonalCharpoly A) :
    A = binomialTransform (fun i => A i i) :=
  classification_charpoly_forward_of_zero_tail zero_tail_boundary n A hl hs hd hg

/-- Britnell--Wildon, Conjecture 2.6 / MathDB 349778, in the literal source convention. -/
theorem mathdb349778 (n : ℕ) (A : Mat n) (hs : Stochastic A)
    (hd : DistinctEigenvalues A) :
    GlobalAntiDiagonalEigenvalue A ↔ ∃ a : Vec n, A = binomialTransform a :=
  classification_iff_of_zero_tail zero_tail_boundary n A hs hd

/-- The same endpoint packaged as the proposition defined before implementation. -/
theorem mathdb349778_all : MathDB349778 := mathdb349778

/-- A two-dimensional instance checks that the literal hypotheses and property coexist. -/
theorem classification_nonvacuous :
    ∃ A : Mat 2, Stochastic A ∧ DistinctEigenvalues A ∧ GlobalAntiDiagonalEigenvalue A := by
  let a : Vec 2 := ![1, 1/2]
  refine ⟨binomialTransform a, ⟨?_, ?_⟩, ?_, transform_global_eigenvalue a⟩
  · intro i j
    rw [show binomialTransform a = !![(1:ℝ),0;1-1/2,1/2] by
      simpa [a] using transform_two (1:ℝ) (1/2)]
    fin_cases i <;> fin_cases j <;> norm_num
  · intro i
    rw [transform_row_sum]
    norm_num [a]
  · apply (lower_distinct_iff _ (transform_lower a)).mpr
    intro i j h
    simp only [transform_diag] at h
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [a] at h

#print axioms classification_charpoly_forward
#print axioms mathdb349778
#print axioms mathdb349778_all
#print axioms classification_nonvacuous
end Classification349778
```

