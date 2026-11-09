import FrameInequality
import BoundaryChecks

set_option autoImplicit false

open Matrix
namespace FourProjection

/-- The literal frame endpoint specializes to four empty column spaces in any ambient dimension. -/
theorem all_empty_frame_boundary {N : Type*} [Fintype N] [DecidableEq N] :
    let Z : Matrix N N ℂ := 0
    let Zn := mpInvSqrt (Z + Z) * Z * mpInvSqrt (Z + Z)
    (trace (Zn * Zn + Zn * Zn)).re ≤ (trace (Z * Z + Z * Z)).re := by
  let e : Matrix N (Fin 0) ℂ := 0
  have he : eᴴ * e = 1 := Subsingleton.elim _ _
  have hi : Function.Injective (fromCols e e).mulVec := fun _ _ _ => Subsingleton.elim _ _
  have ho : eᴴ * e = 0 := Subsingleton.elim _ _
  have h := four_frame_inequality e e e e he he he he hi hi ho ho
  simpa only [e, Matrix.conjTranspose_zero, Matrix.zero_mul] using h

/-- Empty ambient space is allowed as well. -/
example :
    let Z : Matrix (Fin 0) (Fin 0) ℂ := 0
    let Zn := mpInvSqrt (Z + Z) * Z * mpInvSqrt (Z + Z)
    (trace (Zn * Zn + Zn * Zn)).re ≤ (trace (Z * Z + Z * Z)).re :=
  all_empty_frame_boundary

end FourProjection
