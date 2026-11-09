import CountFourier
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open scoped Matrix BigOperators
namespace ChanLevine
variable {R : Type*} [CommRing R]

def dominoMatrix (z g : R) : Matrix (Fin 2) (Fin 2) R := !![1+z, -z*g; g, 0]

theorem domino_det (z g : R) : (dominoMatrix z g).det = z*g^2 := by
  simp [dominoMatrix, Matrix.det_fin_two]
  ring

theorem two_cayley_hamilton (P : Matrix (Fin 2) (Fin 2) R) :
    P^2 - P.trace • P + P.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two,
      Fin.sum_univ_two] <;> ring

theorem two_lucas_matrix (P : Matrix (Fin 2) (Fin 2) R) (r : ℕ) :
    P^(r+2) = P.trace • P^(r+1) - P.det • P^r := by
  have h := congrArg (fun A => A * P^r) (two_cayley_hamilton P)
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, one_mul, zero_mul] at h
  rw [← pow_add, ← pow_succ'] at h
  have he : 2+r = r+2 := by omega
  rw [he] at h
  apply sub_eq_zero.mp
  calc
    _ = P^(r+2) - P.trace • P^(r+1) + P.det • P^r := by abel
    _ = 0 := h

theorem two_lucas_trace (P : Matrix (Fin 2) (Fin 2) R) (r : ℕ) :
    (P^(r+2)).trace = P.trace * (P^(r+1)).trace - P.det * (P^r).trace := by
  rw [two_lucas_matrix, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  rfl
end ChanLevine
