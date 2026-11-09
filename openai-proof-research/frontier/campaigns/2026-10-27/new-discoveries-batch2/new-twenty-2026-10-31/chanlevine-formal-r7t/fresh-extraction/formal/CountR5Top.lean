import CountR4Period
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Polynomial
namespace ChanLevine.Round5
open Round3 Round4

variable {F : Type*} [Field F]

def topMatrix (z : F) (r : ℕ) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => (transferProduct z r i j).coeff r

def linearMatrix (z : F) : Matrix (Fin 2) (Fin 2) F := !![0,z; -1,0]

theorem factor_top (z : F) (r : ℕ) :
    (fun i j => (transferFactor z r i j).coeff 1) = z^r • linearMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transferFactor, dominoMatrix, linearMatrix, Polynomial.coeff_one, ← map_pow] <;> ring

theorem top_zero (z : F) : topMatrix z 0 = 1 := by
  ext i j
  simp [topMatrix, transferProduct, orderedProduct, Matrix.one_apply]
  split_ifs <;> simp

theorem top_succ (z : F) (r : ℕ) :
    topMatrix z (r+1) = topMatrix z r * (z^r • linearMatrix z) := by
  rw [← factor_top]
  ext i j
  change ((transferProduct z r * transferFactor z r) i j).coeff (r+1) = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Polynomial.coeff_add]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (transferProduct_degree z r _ _)
      (transferFactor_degree z r _ _),
    Polynomial.coeff_mul_add_eq_of_natDegree_le (transferProduct_degree z r _ _)
      (transferFactor_degree z r _ _)]
  change _ = ∑ k : Fin 2, (transferProduct z r i k).coeff r * (transferFactor z r k j).coeff 1
  rw [Fin.sum_univ_two]

theorem linear_square (z : F) : linearMatrix z * linearMatrix z = (-z) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linearMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem top_even (z : F) (s : ℕ) :
    topMatrix z (2*s) = ((-1 : F)^s * z^(2*s*s)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction s with
  | zero => simp [top_zero]
  | succ s ih =>
    rw [show 2*(s+1) = (2*s+1)+1 by omega, top_succ, top_succ, ih]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_assoc,
      linear_square, mul_one]
    rw [show (2*s+1+1)*(s+1) = 2*(s*s) + 2*s + (2*s+1) + 1 by ring]
    simp only [pow_add, pow_succ]
    congr 1
    ring

theorem top_odd_trace (z : F) (s : ℕ) : (topMatrix z (2*s+1)).trace = 0 := by
  rw [top_succ, top_even]
  simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, linearMatrix,
    Matrix.trace, Fin.sum_univ_two]

theorem trace_top (z : F) (r : ℕ) :
    ((transferProduct z r).trace).coeff r = (topMatrix z r).trace := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, topMatrix]

theorem primitive_top {z : F} {e : ℕ} (hz : z^e = 1) :
    ((transferProduct z e).trace).coeff e = (parityCoefficient e : F) := by
  rw [trace_top]
  by_cases ho : e % 2 = 1
  · have he : e = 2*(e/2)+1 := by omega
    rw [he, top_odd_trace]
    simp [parityCoefficient, ho, ← he]
  · have he : e = 2*(e/2) := by omega
    rw [he, top_even, Matrix.trace_smul]
    have hp : z^(2*(e/2)*(e/2)) = 1 := by
      rw [← he, pow_mul, hz, one_pow]
    rw [hp]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, parityCoefficient, ho, ← he]
    ring

theorem primitiveTopCoefficient : PrimitiveTopCoefficient := by
  intro n _ _ k
  exact primitive_top (frequencyRoot_pow n k)

end ChanLevine.Round5
