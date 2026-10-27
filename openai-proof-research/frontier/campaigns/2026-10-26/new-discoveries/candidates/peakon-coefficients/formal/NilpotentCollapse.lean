import RankTwo

set_option autoImplicit false
set_option warningAsError true

namespace PeakonCoefficients

open Matrix Polynomial

variable {K : Type*} [Field K]
variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

theorem strict_upper_power_zero (B : Matrix n n K)
    (htri : B.IsUpperTriangular) (hdiag : ∀ i, B i i = 0) :
    B ^ Fintype.card n = 0 := by
  have hc : B.charpoly = X ^ Fintype.card n := by
    rw [Matrix.charpoly_of_isUpperTriangular B htri]
    simp [hdiag]
  have h := Matrix.aeval_self_charpoly B
  rw [hc] at h
  simpa using h

theorem strict_upper_scaled_det (B : Matrix n n K) (t : K)
    (htri : B.IsUpperTriangular) (hdiag : ∀ i, B i i = 0) :
    (1 - t • B).det = 1 := by
  have ht : (1 - t • B).IsUpperTriangular := by
    intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    simp [Matrix.sub_apply, hne, htri hji]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [hdiag]

def finiteResolvent (B : Matrix n n K) (t : K) : Matrix n n K :=
  ∑ i ∈ Finset.range (Fintype.card n), (t • B) ^ i

theorem finiteResolvent_mul (B : Matrix n n K) (t : K)
    (htri : B.IsUpperTriangular) (hdiag : ∀ i, B i i = 0) :
    finiteResolvent B t * (1 - t • B) = 1 := by
  have hz : (t • B) ^ Fintype.card n = 0 := by
    rw [_root_.smul_pow, strict_upper_power_zero B htri hdiag, smul_zero]
  rw [finiteResolvent, geom_sum_mul_neg, hz, sub_zero]

theorem mul_finiteResolvent (B : Matrix n n K) (t : K)
    (htri : B.IsUpperTriangular) (hdiag : ∀ i, B i i = 0) :
    (1 - t • B) * finiteResolvent B t = 1 := by
  have hz : (t • B) ^ Fintype.card n = 0 := by
    rw [_root_.smul_pow, strict_upper_power_zero B htri hdiag, smul_zero]
  rw [finiteResolvent, mul_neg_geom_sum, hz, sub_zero]

theorem strict_upper_spectral_collapse [CharZero K] (B : Matrix n n K) (t lam xi gamma : K)
    (u v : n → K)
    (htri : B.IsUpperTriangular) (hdiag : ∀ i, B i i = 0)
    (hskew : B - B.transpose = vecMulVec u v - vecMulVec v u)
    (hcurve : xi ^ 2 = lam ^ 2 + gamma * lam + 1) :
    (1 - t • (B + ((lam + xi - 1) / 2) • vecMulVec u v +
      ((lam - xi + 1) / 2) • vecMulVec v u)).det =
      1 - lam * t / 2 * (v ⬝ᵥ (finiteResolvent B t *ᵥ u) +
        u ⬝ᵥ (finiteResolvent B t *ᵥ v)) -
        gamma * lam * t / 4 * (v ⬝ᵥ (finiteResolvent B t *ᵥ u) -
          u ⬝ᵥ (finiteResolvent B t *ᵥ v)) := by
  exact determinant_spectral_collapse B (finiteResolvent B t) t lam xi gamma u v
    (finiteResolvent_mul B t htri hdiag) (mul_finiteResolvent B t htri hdiag)
    (strict_upper_scaled_det B t htri hdiag) hskew hcurve

end PeakonCoefficients
