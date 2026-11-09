import NilpotentCollapse

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix

variable {K : Type*} [Field K] [CharZero K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

def upperKernel (u v : n → K) : Matrix n n K :=
  fun i j => if i < j then u i * v j - v i * u j else 0

omit [CharZero K] [Fintype n] [DecidableEq n] in
theorem upperKernel_triangular (u v : n → K) : (upperKernel u v).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [upperKernel, not_lt_of_ge (le_of_lt hji)]

omit [CharZero K] [Fintype n] [DecidableEq n] in
theorem upperKernel_diagonal (u v : n → K) (i : n) : upperKernel u v i i = 0 := by
  simp [upperKernel]

omit [CharZero K] [Fintype n] [DecidableEq n] in
theorem upperKernel_skew (u v : n → K) :
    upperKernel u v - (upperKernel u v).transpose = vecMulVec u v - vecMulVec v u := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [upperKernel, h, not_lt_of_ge (le_of_lt h), Matrix.vecMulVec_apply]
  · subst j
    simp [upperKernel, Matrix.vecMulVec_apply, mul_comm]
  · simp [upperKernel, h, not_lt_of_ge (le_of_lt h), Matrix.vecMulVec_apply]
    ring

def skewPart (u v : n → K) : Matrix n n K :=
  (1 / 2 : K) • (vecMulVec u v - vecMulVec v u)

def symmetricPart (u v : n → K) : Matrix n n K :=
  (1 / 2 : K) • (vecMulVec u v + vecMulVec v u)

def algebraicLax (u v : n → K) (lam xi : K) : Matrix n n K :=
  upperKernel u v - skewPart u v + lam • symmetricPart u v + xi • skewPart u v

omit [Fintype n] [DecidableEq n] in
theorem algebraicLax_rank_two (u v : n → K) (lam xi : K) :
    algebraicLax u v lam xi = upperKernel u v +
      ((lam + xi - 1) / 2) • vecMulVec u v +
      ((lam - xi + 1) / 2) • vecMulVec v u := by
  ext i j
  simp only [algebraicLax, skewPart, symmetricPart, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem algebraicLax_det_collapse (u v : n → K) (t lam xi gamma : K)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - t • algebraicLax u v lam xi).det =
      1 - lam * t / 2 *
        (v ⬝ᵥ (finiteResolvent (upperKernel u v) t *ᵥ u) +
          u ⬝ᵥ (finiteResolvent (upperKernel u v) t *ᵥ v)) -
        gamma * lam * t / 4 *
        (v ⬝ᵥ (finiteResolvent (upperKernel u v) t *ᵥ u) -
          u ⬝ᵥ (finiteResolvent (upperKernel u v) t *ᵥ v)) := by
  rw [algebraicLax_rank_two]
  exact strict_upper_spectral_collapse (upperKernel u v) t lam xi gamma u v
    (upperKernel_triangular u v) (upperKernel_diagonal u v) (upperKernel_skew u v) hcurve

end PeakonCoefficients
