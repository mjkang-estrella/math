import Mathlib

/-!
Uncredited algebraic checks for the prior-art exclusion of Zhou 5.8.
This file is NOT a formal proof of the source conjecture. In particular it
does not assert any infinite-series, Jacobi, integral, or coefficient bridge.
-/
namespace ZhouExclusionChecks

theorem reciprocal_kernel (s c : ℝ) (hs : s ≠ 0) (hc : c ≠ 0) :
    1 / s ^ 2 + 1 / c ^ 2 = 4 * (c ^ 2 + s ^ 2) / (2 * s * c) ^ 2 := by
  field_simp
  <;> ring

theorem miura_identity (t w v : ℝ)
    (hv : v ^ 2 = (1 - t) ^ 2 - 2 * (1 + t) * w ^ 2 + w ^ 4) :
    (-2 * (1 + t) + 6 * w ^ 2) * v + 2 * v ^ 2 +
        2 * w * (-2 * (1 + t) * w + 2 * w ^ 3) =
      3 * (v + w ^ 2) ^ 2 - 2 * (1 + t) * (v + w ^ 2) - (1 - t) ^ 2 := by
  nlinarith [hv]

theorem centered_miura (t u : ℝ) :
    3 * u ^ 2 - 2 * (1 + t) * u - (1 - t) ^ 2 =
      3 * (u - (1 + t) / 3) ^ 2 - 4 / 3 * (1 - t + t ^ 2) := by
  ring

theorem symmetric_potential (t : ℝ) :
    1 - (1 - t) + (1 - t) ^ 2 = 1 - t + t ^ 2 := by ring

theorem midpoint_antisymmetric (f : ℝ → ℝ)
    (h : ∀ t, f (1 - t) = -f t) : f (1 / 2) = 0 := by
  have hh := h (1 / 2)
  norm_num at hh
  linarith

end ZhouExclusionChecks

#print axioms ZhouExclusionChecks.reciprocal_kernel
#print axioms ZhouExclusionChecks.miura_identity
#print axioms ZhouExclusionChecks.centered_miura
#print axioms ZhouExclusionChecks.symmetric_potential
#print axioms ZhouExclusionChecks.midpoint_antisymmetric
