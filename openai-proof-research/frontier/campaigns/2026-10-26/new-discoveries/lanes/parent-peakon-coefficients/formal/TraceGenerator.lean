import UpperFamily

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

omit [CharZero K] [LinearOrder n] [DecidableEq n] in
theorem trace_outer_mul (u v : n → K) (R : Matrix n n K) :
    Matrix.trace (vecMulVec u v * R) = v ⬝ᵥ (R *ᵥ u) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

def hamiltonianDirection (u v : n → K) (gamma : K) : Matrix n n K :=
  symmetricPart u v + (gamma / 2) • skewPart u v

omit [LinearOrder n] [DecidableEq n] in
theorem trace_hamiltonianDirection (u v : n → K) (gamma : K) (R : Matrix n n K) :
    Matrix.trace (hamiltonianDirection u v gamma * R) =
      (v ⬝ᵥ (R *ᵥ u) + u ⬝ᵥ (R *ᵥ v)) / 2 +
        gamma / 4 * (v ⬝ᵥ (R *ᵥ u) - u ⬝ᵥ (R *ᵥ v)) := by
  simp only [hamiltonianDirection, symmetricPart, skewPart, Matrix.add_mul,
    Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, trace_outer_mul]
  ring

def rawHamiltonian (u v : n → K) (gamma : K) (k : ℕ) : K :=
  (k : K) * Matrix.trace (hamiltonianDirection u v gamma * upperKernel u v ^ (k - 1))

def hamiltonianGenerator (u v : n → K) (gamma t : K) : K :=
  t * Matrix.trace (hamiltonianDirection u v gamma * finiteResolvent (upperKernel u v) t)

theorem det_eq_one_sub_generator (u v : n → K) (t lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - t • algebraicLax u v lam xi).det =
      1 - lam * hamiltonianGenerator u v gamma t := by
  rw [algebraicLax_det_collapse u v t lam xi gamma hcurve,
    hamiltonianGenerator, trace_hamiltonianDirection]
  ring

omit [CharZero K] in
theorem hamiltonianGenerator_finite_sum (u v : n → K) (gamma t : K) :
    hamiltonianGenerator u v gamma t =
      ∑ i ∈ Finset.range (Fintype.card n),
        t ^ (i + 1) * Matrix.trace (hamiltonianDirection u v gamma * upperKernel u v ^ i) := by
  simp only [hamiltonianGenerator, finiteResolvent,
    Matrix.trace_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.smul_pow, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, pow_succ]
  ring

theorem rawHamiltonian_normalization (u v : n → K) (gamma : K) (k : ℕ) :
    rawHamiltonian u v gamma (k + 1) / (k + 1 : K) =
      Matrix.trace (hamiltonianDirection u v gamma * upperKernel u v ^ k) := by
  simp only [rawHamiltonian, Nat.add_sub_cancel]
  have hk : (k + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

end PeakonCoefficients
