import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace TraceFormal
abbrev Mat (K : Type*) := Matrix (Fin 3) (Fin 3) K
abbrev tr {K : Type*} [AddCommMonoid K] (A : Mat K) := Matrix.trace A
/-- Signed cycle expansion, matching the alternating convention in the bound verifier. -/
def fundamental {K : Type*} [CommRing K] (A B C D : Mat K) : K :=
tr (A) * tr (B) * tr (C) * tr (D)
  - tr (A) * tr (B) * tr (C * D)
  - tr (A) * tr (B * C) * tr (D)
  + tr (A) * tr (B * C * D)
  + tr (A) * tr (B * D * C)
  - tr (A) * tr (B * D) * tr (C)
  - tr (A * B) * tr (C) * tr (D)
  + tr (A * B) * tr (C * D)
  + tr (A * B * C) * tr (D)
  - tr (A * B * C * D)
  - tr (A * B * D * C)
  + tr (A * B * D) * tr (C)
  + tr (A * C * B) * tr (D)
  - tr (A * C * D * B)
  - tr (A * C) * tr (B) * tr (D)
  + tr (A * C * D) * tr (B)
  + tr (A * C) * tr (B * D)
  - tr (A * C * B * D)
  - tr (A * D * C * B)
  + tr (A * D * B) * tr (C)
  + tr (A * D * C) * tr (B)
  - tr (A * D) * tr (B) * tr (C)
  - tr (A * D * B * C)
  + tr (A * D) * tr (B * C)
/-- Actual full-matrix fundamental identity; no traceless hypotheses. -/
theorem fundamental_matrix {K : Type*} [CommRing K] (A B C D : Mat K) :
    fundamental A B C D = 0 := by
  simp only [fundamental, tr, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring
#print axioms fundamental_matrix
end TraceFormal
