import Mathlib

open Matrix Unitary
open scoped ComplexOrder

namespace FourProjection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The support inverse square root on positive semidefinite inputs, defined by total CFC.
The scalar function takes value zero at zero. -/
noncomputable def mpInvSqrt (A : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) A

/-- Exact finite-spectrum representation, including all zero eigenvalues. -/
theorem mpInvSqrt_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    mpInvSqrt A =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [mpInvSqrt, hA.cfc_eq]
  rfl

/-- An arbitrary scalar function preserves intertwiners of real diagonal matrices. -/
theorem diagonal_intertwine (a : m → ℝ) (b : n → ℝ) (T : Matrix m n ℂ)
    (h : diagonal (fun i => (a i : ℂ)) * T = T * diagonal (fun j => (b j : ℂ)))
    (f : ℝ → ℝ) :
    diagonal (fun i => (f (a i) : ℂ)) * T = T * diagonal (fun j => (f (b j) : ℂ)) := by
  ext i j
  have hij := congrArg (fun M : Matrix m n ℂ => M i j) h
  simp only [diagonal_mul, mul_diagonal] at hij ⊢
  by_cases hab : a i = b j
  · rw [hab, mul_comm]
  · have hne : (a i : ℂ) - (b j : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (fun hh => hab (Complex.ofReal_injective hh))
    have hz : T i j = 0 := (mul_eq_zero.mp (show ((a i : ℂ) - (b j : ℂ)) * T i j = 0 by
      linear_combination hij)).resolve_left hne
    simp [hz]

/-- Functional calculus preserves arbitrary rectangular intertwiners of Hermitian matrices. -/
theorem hermitian_cfc_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (T : Matrix m n ℂ)
    (h : A * T = T * B) (f : ℝ → ℝ) : cfc f A * T = T * cfc f B := by
  let V : Matrix m m ℂ := hA.eigenvectorUnitary
  let W : Matrix n n ℂ := hB.eigenvectorUnitary
  have hv : star V * V = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hv' : V * star V = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hw : star W * W = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hw' : W * star W = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have ha : A = V * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star V := hA.spectral_theorem
  have hb : B = W * diagonal (fun i => (hB.eigenvalues i : ℂ)) * star W := hB.spectral_theorem
  have hd : diagonal (fun i => (hA.eigenvalues i : ℂ)) * (star V * T * W) =
      (star V * T * W) * diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
    have h' := congrArg (fun X : Matrix m n ℂ => star V * X * W) h
    rw [ha, hb] at h'
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc (star V) V, hv, Matrix.one_mul,
      ← Matrix.mul_assoc (star W) W, hw, Matrix.mul_one] using h'
  have hd' := diagonal_intertwine _ _ _ hd f
  have h' := congrArg (fun X : Matrix m n ℂ => V * X * star W) hd'
  rw [hA.cfc_eq, hB.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  change V * diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * star V * T =
    T * (W * diagonal (fun i => (f (hB.eigenvalues i) : ℂ)) * star W)
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc W (star W), hw', Matrix.mul_one,
    ← Matrix.mul_assoc V (star V), hv', Matrix.one_mul] using h'

/-- The Moore–Penrose inverse-square-root bridge. No rank assumption is needed. -/
theorem mpInvSqrt_mul (E : Matrix m n ℂ) :
    mpInvSqrt (E * Eᴴ) * E = E * mpInvSqrt (Eᴴ * E) := by
  exact hermitian_cfc_intertwine (isHermitian_mul_conjTranspose_self E)
    (isHermitian_conjTranspose_mul_self E) E (Matrix.mul_assoc _ _ _) _

/-- The inverse square root used on the positive definite column Gram matrix.
It has the same total CFC definition; cancellation is proved under positive definiteness. -/
noncomputable def invSqrt (A : Matrix n n ℂ) : Matrix n n ℂ := mpInvSqrt A

/-- The CFC inverse square root is Hermitian, even without hypotheses on its input. -/
theorem mpInvSqrt_isHermitian (A : Matrix n n ℂ) : (mpInvSqrt A).IsHermitian := by
  exact (IsSelfAdjoint.cfc (f := fun t : ℝ => (Real.sqrt t)⁻¹) (a := A)).isHermitian

/-- The inverse square root has nonnegative eigenvalues. -/
theorem mpInvSqrt_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (mpInvSqrt A).PosSemidef := by
  rw [mpInvSqrt_spectral hA]
  have hd : (diagonal (fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast inv_nonneg.mpr (Real.sqrt_nonneg (hA.eigenvalues i))
  simpa only [star_eq_conjTranspose] using
    hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix n n ℂ)

private theorem continuousOn_matrix_spectrum (f : ℝ → ℝ) (A : Matrix n n ℂ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

private theorem matrix_cfc_mul (f g : ℝ → ℝ) (A : Matrix n n ℂ) :
    cfc (fun t => f t * g t) A = cfc f A * cfc g A :=
  cfc_mul f g A (continuousOn_matrix_spectrum f A) (continuousOn_matrix_spectrum g A)

/-- Exact cancellation on a positive definite matrix, proved from its positive spectrum. -/
theorem mpInvSqrt_sandwich_of_posDef {A : Matrix n n ℂ} (hA : A.PosDef) :
    mpInvSqrt A * A * mpInvSqrt A = 1 := by
  have hscalar (i : n) :
      (Real.sqrt (hA.1.eigenvalues i))⁻¹ * hA.1.eigenvalues i *
        (Real.sqrt (hA.1.eigenvalues i))⁻¹ = 1 := by
    have hp := hA.eigenvalues_pos i
    have hs := Real.sq_sqrt hp.le
    have hn := (Real.sqrt_pos.2 hp).ne'
    field_simp
    nlinarith
  calc
    _ = cfc (fun t : ℝ => (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹) A := by
      rw [matrix_cfc_mul, matrix_cfc_mul, cfc_id' ℝ A hA.1.isSelfAdjoint]
      rfl
    _ = 1 := by
      rw [hA.1.cfc_eq]
      unfold Matrix.IsHermitian.cfc
      have hd : diagonal (RCLike.ofReal ∘
          (fun t : ℝ => (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹) ∘ hA.1.eigenvalues) =
          (1 : Matrix n n ℂ) := by
        simp only [Function.comp_def, hscalar, map_one, diagonal_one]
      rw [hd, map_one]

/-- The canonical rectangular polar frame. -/
noncomputable def polarFrame (E : Matrix m n ℂ) : Matrix m n ℂ := E * invSqrt (Eᴴ * E)

/-- The canonical polar frame equals the literal ambient Moore–Penrose normalization. -/
theorem polarFrame_eq_mpInvSqrt_mul (E : Matrix m n ℂ) :
    polarFrame E = mpInvSqrt (E * Eᴴ) * E := (mpInvSqrt_mul E).symm

omit [DecidableEq m] in
/-- An injective rectangular matrix has an isometric canonical polar frame.
No nonemptiness hypothesis is required on either index type. -/
theorem polarFrame_isometry (E : Matrix m n ℂ) (hE : Function.Injective E.mulVec) :
    (polarFrame E)ᴴ * polarFrame E = 1 := by
  have hp : (Eᴴ * E).PosDef := Matrix.PosDef.conjTranspose_mul_self E hE
  have hh := (mpInvSqrt_isHermitian (Eᴴ * E)).eq
  unfold polarFrame invSqrt
  rw [conjTranspose_mul, hh]
  simpa only [Matrix.mul_assoc] using mpInvSqrt_sandwich_of_posDef hp

/-- Exact normalized congruence, valid for every coordinate matrix C and every E. -/
theorem normalized_congruence (E : Matrix m n ℂ) (C : Matrix n n ℂ) :
    mpInvSqrt (E * Eᴴ) * (E * C * Eᴴ) * mpInvSqrt (E * Eᴴ) =
      polarFrame E * C * (polarFrame E)ᴴ := by
  rw [polarFrame_eq_mpInvSqrt_mul, conjTranspose_mul,
    (mpInvSqrt_isHermitian (E * Eᴴ)).eq]
  simp only [Matrix.mul_assoc]

/-- The bridge with the column-side name used in the polar decomposition. -/
theorem mpInvSqrt_mul_eq_mul_invSqrt (E : Matrix m n ℂ) :
    mpInvSqrt (E * Eᴴ) * E = E * invSqrt (Eᴴ * E) := mpInvSqrt_mul E

@[simp] theorem mpInvSqrt_zero : mpInvSqrt (0 : Matrix n n ℂ) = 0 := by
  simp [mpInvSqrt]

/-- The support inverse square root annihilates the entire kernel. -/
theorem mpInvSqrt_mulVec_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (x : n → ℂ) (hx : A *ᵥ x = 0) : mpInvSqrt A *ᵥ x = 0 := by
  have h0 : A * replicateCol Unit x = replicateCol Unit x * (0 : Matrix Unit Unit ℂ) := by
    rw [← replicateCol_mulVec, hx, replicateCol_zero, Matrix.mul_zero]
  have hh := hermitian_cfc_intertwine hA (isHermitian_zero (n := Unit) (α := ℂ))
    (replicateCol Unit x) h0 (fun t : ℝ => (Real.sqrt t)⁻¹)
  change mpInvSqrt A * replicateCol Unit x = replicateCol Unit x * mpInvSqrt 0 at hh
  rw [mpInvSqrt_zero, Matrix.mul_zero, ← replicateCol_mulVec, replicateCol_eq_zero] at hh
  exact hh

/-- An orthogonal projection on column coordinates remains an orthogonal projection
under the exact ambient normalization. -/
theorem normalized_congruence_is_projection (E : Matrix m n ℂ)
    (hE : Function.Injective E.mulVec) (C : Matrix n n ℂ)
    (hC : C.IsHermitian) (hCC : C * C = C) :
    let P := mpInvSqrt (E * Eᴴ) * (E * C * Eᴴ) * mpInvSqrt (E * Eᴴ)
    P.IsHermitian ∧ P * P = P := by
  dsimp only
  rw [normalized_congruence]
  constructor
  · show (polarFrame E * C * (polarFrame E)ᴴ)ᴴ = polarFrame E * C * (polarFrame E)ᴴ
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hC.eq, Matrix.mul_assoc]
  · calc
      _ = polarFrame E * (C * ((polarFrame E)ᴴ * polarFrame E) * C) * (polarFrame E)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [polarFrame_isometry E hE, Matrix.mul_one, hCC]

/-- The orthogonal selector for a finite set of column coordinates. -/
def coordinateProjection (s : Finset n) : Matrix n n ℂ :=
  diagonal (fun i => if i ∈ s then 1 else 0)

omit [Fintype n] in
theorem coordinateProjection_isHermitian (s : Finset n) :
    (coordinateProjection s).IsHermitian := by
  show (coordinateProjection s)ᴴ = coordinateProjection s
  simp [coordinateProjection, diagonal_conjTranspose]

theorem coordinateProjection_idempotent (s : Finset n) :
    coordinateProjection s * coordinateProjection s = coordinateProjection s := by
  rw [coordinateProjection, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The literal normalized coordinate-subspace projection, with no choice of frame. -/
theorem normalized_coordinateProjection (E : Matrix m n ℂ) (s : Finset n) :
    mpInvSqrt (E * Eᴴ) * (E * coordinateProjection s * Eᴴ) * mpInvSqrt (E * Eᴴ) =
      polarFrame E * coordinateProjection s * (polarFrame E)ᴴ :=
  normalized_congruence E (coordinateProjection s)

/-- In particular the normalized coordinate selector is an orthogonal projection. -/
theorem normalized_coordinateProjection_is_projection (E : Matrix m n ℂ)
    (hE : Function.Injective E.mulVec) (s : Finset n) :
    let P := mpInvSqrt (E * Eᴴ) * (E * coordinateProjection s * Eᴴ) * mpInvSqrt (E * Eᴴ)
    P.IsHermitian ∧ P * P = P :=
  normalized_congruence_is_projection E hE _
    (coordinateProjection_isHermitian s) (coordinateProjection_idempotent s)

end FourProjection
