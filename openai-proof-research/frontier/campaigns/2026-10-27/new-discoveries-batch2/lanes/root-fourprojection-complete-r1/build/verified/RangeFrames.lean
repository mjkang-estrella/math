import ProjectionFrames

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FourProjection
open scoped BigOperators Matrix ComplexConjugate

/-- Spectral reconstruction using exactly the eigenvalue-one columns. -/
theorem projectionFrame_mul_adjoint {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    projectionFrame hP * (projectionFrame hP)ᴴ = P := by
  classical
  have hs : P = (hP.eigenvectorUnitary : Matrix N N ℂ) *
      Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) *
      (hP.eigenvectorUnitary : Matrix N N ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using! hP.spectral_theorem
  ext a b
  conv_rhs => rw [hs]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  change (∑ i : ProjectionFrameIndex hP,
    hP.eigenvectorUnitary a i.val * conj (hP.eigenvectorUnitary b i.val)) = _
  apply Fintype.sum_of_injective (fun i : ProjectionFrameIndex hP => i.val)
      Subtype.val_injective
  · intro i hi
    have hi1 : hP.eigenvalues i ≠ 1 := by
      intro hh
      exact hi ⟨⟨i, hh⟩, rfl⟩
    have hi0 := (projection_eigenvalue_zero_or_one P hP hPP i).resolve_right hi1
    simp [hi0]
  · intro i
    simp [i.property]

/-- The canonical columns are fixed by the original projection. -/
theorem projection_mul_frame {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    P * projectionFrame hP = projectionFrame hP := by
  calc
    _ = (projectionFrame hP * (projectionFrame hP)ᴴ) * projectionFrame hP :=
      congrArg (fun A => A * projectionFrame hP) (projectionFrame_mul_adjoint hP hPP).symm
    _ = projectionFrame hP := by
      rw [Matrix.mul_assoc, projectionFrame_isometry, Matrix.mul_one]

/-- An isometric rectangular matrix is injective, also for empty column types. -/
theorem isometry_mulVec_injective {N I : Type*} [Fintype N] [Fintype I]
    [DecidableEq I] (p : Matrix N I ℂ) (hp : pᴴ * p = 1) :
    Function.Injective p.mulVec := by
  intro x y h
  have hh := congrArg pᴴ.mulVec h
  simpa only [Matrix.mulVec_mulVec, hp, Matrix.one_mulVec] using hh

theorem projectionFrame_mulVec_injective {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) :
    Function.Injective (projectionFrame hP).mulVec := by
  classical
  exact isometry_mulVec_injective _ (projectionFrame_isometry hP)

/-- Membership in the image of an idempotent is its fixed-vector condition. -/
theorem mem_range_projection_iff {N : Type*} [Fintype N]
    (P : Matrix N N ℂ) (hPP : P * P = P) (v : N → ℂ) :
    v ∈ LinearMap.range P.mulVecLin ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [Matrix.mulVec_mulVec, hPP]
  · intro h
    exact ⟨v, h⟩

/-- The canonical coefficients pᴴv reconstruct precisely the fixed vectors. -/
theorem projectionFrame_reconstruct {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (v : N → ℂ) (hv : P *ᵥ v = v) :
    projectionFrame hP *ᵥ ((projectionFrame hP)ᴴ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, projectionFrame_mul_adjoint hP hPP, hv]

theorem mem_range_frame_iff {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P) (v : N → ℂ) :
    v ∈ LinearMap.range (projectionFrame hP).mulVecLin ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    change P *ᵥ (projectionFrame hP *ᵥ w) = projectionFrame hP *ᵥ w
    rw [Matrix.mulVec_mulVec, projection_mul_frame hP hPP]
  · intro hv
    exact ⟨(projectionFrame hP)ᴴ *ᵥ v, projectionFrame_reconstruct hP hPP v hv⟩

theorem projectionFrame_range {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    LinearMap.range (projectionFrame hP).mulVecLin = LinearMap.range P.mulVecLin := by
  ext v
  rw [mem_range_frame_iff hP hPP, mem_range_projection_iff P hPP]

/-- Literal source range disjointness is equivalent to the fixed-vector version. -/
theorem range_inf_eq_bot_iff {N : Type*} [Fintype N]
    (P R : Matrix N N ℂ) (hPP : P * P = P) (hRR : R * R = R) :
    LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥ ↔
      ∀ v : N → ℂ, P *ᵥ v = v → R *ᵥ v = v → v = 0 := by
  rw [Submodule.eq_bot_iff]
  simp only [Submodule.mem_inf, mem_range_projection_iff P hPP,
    mem_range_projection_iff R hRR, and_imp]

/-- Every vector in the original range has unique canonical frame coordinates. -/
theorem projectionFrame_coordinates {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (v : N → ℂ) (hv : v ∈ LinearMap.range P.mulVecLin) :
    ∃! x : ProjectionFrameIndex hP → ℂ, projectionFrame hP *ᵥ x = v := by
  refine ⟨(projectionFrame hP)ᴴ *ᵥ v,
    projectionFrame_reconstruct hP hPP v ((mem_range_projection_iff P hPP v).mp hv), ?_⟩
  intro y hy
  apply projectionFrame_mulVec_injective hP
  exact hy.trans (projectionFrame_reconstruct hP hPP v
    ((mem_range_projection_iff P hPP v).mp hv)).symm

/-- The canonical frame maps onto the entire source range. -/
theorem projectionFrame_surjOn_range {N : Type*} [Fintype N] [DecidableEq N]
    {P : Matrix N N ℂ} (hP : P.IsHermitian) (hPP : P * P = P) :
    Set.SurjOn (projectionFrame hP).mulVec Set.univ (LinearMap.range P.mulVecLin) := by
  intro v hv
  obtain ⟨x, hx, _⟩ := projectionFrame_coordinates hP hPP v hv
  exact ⟨x, Set.mem_univ x, hx⟩

/-- The only common fixed vector suffices to make two range frames independent. -/
theorem fromCols_mulVec_injective {N I J : Type*}
    [Fintype N] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (P R : Matrix N N ℂ) (p : Matrix N I ℂ) (r : Matrix N J ℂ)
    (hp : pᴴ * p = 1) (hr : rᴴ * r = 1)
    (hPp : P * p = p) (hRr : R * r = r)
    (hdisj : ∀ v : N → ℂ, P *ᵥ v = v → R *ᵥ v = v → v = 0) :
    Function.Injective (Matrix.fromCols p r).mulVec := by
  have hker : ∀ z : I ⊕ J → ℂ, Matrix.fromCols p r *ᵥ z = 0 → z = 0 := by
    intro z hz
    rw [Matrix.fromCols_mulVec] at hz
    have he : p *ᵥ (z ∘ Sum.inl) = -(r *ᵥ (z ∘ Sum.inr)) := eq_neg_of_add_eq_zero_left hz
    have hpz : p *ᵥ (z ∘ Sum.inl) = 0 := by
      apply hdisj
      · rw [Matrix.mulVec_mulVec, hPp]
      · rw [he, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hRr]
    have hrz : r *ᵥ (z ∘ Sum.inr) = 0 := by
      simpa only [hpz, zero_add] using hz
    have hzi : z ∘ Sum.inl = 0 := isometry_mulVec_injective p hp
      (hpz.trans (Matrix.mulVec_zero p).symm)
    have hzj : z ∘ Sum.inr = 0 := isometry_mulVec_injective r hr
      (hrz.trans (Matrix.mulVec_zero r).symm)
    funext k
    cases k with
    | inl i => exact congrFun hzi i
    | inr j => exact congrFun hzj j
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, hxy, sub_self]

noncomputable def projectionPairFrame {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian) :
    Matrix N (ProjectionFrameIndex hP ⊕ ProjectionFrameIndex hR) ℂ :=
  Matrix.fromCols (projectionFrame hP) (projectionFrame hR)

/-- Source-level full column rank; no assumptions on ambient invertibility or ranks. -/
theorem projectionPairFrame_injective {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian)
    (hPP : P * P = P) (hRR : R * R = R)
    (hdisj : LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥) :
    Function.Injective (projectionPairFrame hP hR).mulVec := by
  classical
  exact fromCols_mulVec_injective P R _ _ (projectionFrame_isometry hP)
    (projectionFrame_isometry hR) (projection_mul_frame hP hPP)
    (projection_mul_frame hR hRR) ((range_inf_eq_bot_iff P R hPP hRR).mp hdisj)

/-- Product with the adjoint is the sum of the two original source projections. -/
theorem projectionPairFrame_mul_adjoint {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian)
    (hPP : P * P = P) (hRR : R * R = R) :
    projectionPairFrame hP hR * (projectionPairFrame hP hR)ᴴ = P + R := by
  simp only [projectionPairFrame, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, projectionFrame_mul_adjoint hP hPP,
    projectionFrame_mul_adjoint hR hRR]

/-- Coordinate projection onto the left summand. -/
def frameSelectorLeft (I J : Type*) [DecidableEq I] : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 1 0 0 0

/-- Coordinate projection onto the right summand. -/
def frameSelectorRight (I J : Type*) [DecidableEq J] : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks 0 0 0 1

theorem fromCols_selector_left {N I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I]
    (p : Matrix N I ℂ) (r : Matrix N J ℂ) :
    Matrix.fromCols p r * frameSelectorLeft I J * (Matrix.fromCols p r)ᴴ = p * pᴴ := by
  simp only [frameSelectorLeft, Matrix.fromCols_mul_fromBlocks,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem fromCols_selector_right {N I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    (p : Matrix N I ℂ) (r : Matrix N J ℂ) :
    Matrix.fromCols p r * frameSelectorRight I J * (Matrix.fromCols p r)ᴴ = r * rᴴ := by
  simp only [frameSelectorRight, Matrix.fromCols_mul_fromBlocks,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem projectionPairFrame_selector_left {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian)
    (hPP : P * P = P) :
    projectionPairFrame hP hR *
      frameSelectorLeft (ProjectionFrameIndex hP) (ProjectionFrameIndex hR) *
      (projectionPairFrame hP hR)ᴴ = P := by
  classical
  rw [projectionPairFrame, fromCols_selector_left, projectionFrame_mul_adjoint hP hPP]

theorem projectionPairFrame_selector_right {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian)
    (hRR : R * R = R) :
    projectionPairFrame hP hR *
      frameSelectorRight (ProjectionFrameIndex hP) (ProjectionFrameIndex hR) *
      (projectionPairFrame hP hR)ᴴ = R := by
  classical
  rw [projectionPairFrame, fromCols_selector_right, projectionFrame_mul_adjoint hR hRR]

theorem fromCols_gram {N I J : Type*} [Fintype N]
    [DecidableEq I] [DecidableEq J]
    (p : Matrix N I ℂ) (r : Matrix N J ℂ) (hp : pᴴ * p = 1) (hr : rᴴ * r = 1) :
    (Matrix.fromCols p r)ᴴ * Matrix.fromCols p r =
      Matrix.fromBlocks 1 (pᴴ * r) (rᴴ * p) 1 := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, hp, hr]

theorem projectionPairFrame_gram {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian) :
    (projectionPairFrame hP hR)ᴴ * projectionPairFrame hP hR =
      Matrix.fromBlocks 1 ((projectionFrame hP)ᴴ * projectionFrame hR)
        ((projectionFrame hR)ᴴ * projectionFrame hP) 1 := by
  classical
  exact fromCols_gram _ _ (projectionFrame_isometry hP) (projectionFrame_isometry hR)

/-- Orthogonal source projections yield zero cross-Gram blocks for any fixed columns. -/
theorem fixed_frames_cross_eq_zero {N I J : Type*}
    [Fintype N] [DecidableEq N]
    {P Q : Matrix N N ℂ} (hP : P.IsHermitian)
    (p : Matrix N I ℂ) (q : Matrix N J ℂ)
    (hPp : P * p = p) (hQq : Q * q = q) (hPQ : P * Q = 0) :
    pᴴ * q = 0 := by
  have hpP : pᴴ * P = pᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP.eq] using congrArg Matrix.conjTranspose hPp
  calc
    pᴴ * q = (pᴴ * P) * (Q * q) := by rw [hpP, hQq]
    _ = pᴴ * (P * Q) * q := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPQ, Matrix.mul_zero, Matrix.zero_mul]

theorem projectionFrames_cross_eq_zero {N : Type*} [Fintype N] [DecidableEq N]
    {P Q : Matrix N N ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hPQ : P * Q = 0) :
    (projectionFrame hP)ᴴ * projectionFrame hQ = 0 :=
  fixed_frames_cross_eq_zero hP _ _ (projection_mul_frame hP hPP)
    (projection_mul_frame hQ hQQ) hPQ

/-- The scalar diagonal of the concatenated Gram matrix is identically one. -/
theorem projectionPairFrame_gram_diag {N : Type*} [Fintype N] [DecidableEq N]
    {P R : Matrix N N ℂ} (hP : P.IsHermitian) (hR : R.IsHermitian) :
    Matrix.diag ((projectionPairFrame hP hR)ᴴ * projectionPairFrame hP hR) = 1 := by
  classical
  rw [projectionPairFrame_gram]
  funext i
  cases i <;> simp [Matrix.diag, Matrix.fromBlocks]

end FourProjection
