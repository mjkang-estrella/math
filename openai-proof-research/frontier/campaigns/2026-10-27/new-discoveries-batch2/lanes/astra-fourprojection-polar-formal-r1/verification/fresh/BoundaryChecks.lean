import PolarFrameBridge

open Matrix FourProjection

-- Both dimensions empty.
example (E : Matrix (Fin 0) (Fin 0) ℂ) : (polarFrame E)ᴴ * polarFrame E = 1 := by
  apply polarFrame_isometry
  intro x y _
  exact Subsingleton.elim x y

-- Nonempty ambient space, empty column space.
example (E : Matrix (Fin 3) (Fin 0) ℂ) : (polarFrame E)ᴴ * polarFrame E = 1 := by
  apply polarFrame_isometry
  intro x y _
  exact Subsingleton.elim x y

-- Empty ambient space: the intertwining identity does not require injectivity.
example (E : Matrix (Fin 0) (Fin 3) ℂ) :
    mpInvSqrt (E * Eᴴ) * E = E * invSqrt (Eᴴ * E) :=
  mpInvSqrt_mul_eq_mul_invSqrt E

-- A genuinely rectangular injective column with a singular 2-by-2 ambient Gram matrix.
example :
    let E : Matrix (Fin 2) (Fin 1) ℂ := Matrix.of fun i _ => if i = 0 then 1 else 0
    (E * Eᴴ).det = 0 ∧ (polarFrame E)ᴴ * polarFrame E = 1 := by
  dsimp only
  constructor
  · rw [Matrix.det_fin_two]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  · apply polarFrame_isometry
    intro x y h
    funext j
    fin_cases j
    have hh := congrFun h 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using hh
