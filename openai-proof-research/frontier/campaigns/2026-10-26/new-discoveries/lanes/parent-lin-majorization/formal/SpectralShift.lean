import SourceDefs

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix Unitary
namespace LinMajorization

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem shift_posSemidef_of_eigenvalues {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (c : ℝ) (h : ∀ i, c ≤ hM.eigenvalues i) :
    (M - (c : ℂ) • 1).PosSemidef := by
  have hd : (diagonal (fun i => ((hM.eigenvalues i-c : ℝ) : ℂ))).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ ((hM.eigenvalues i-c : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (h i)
  have hd' : ((diagonal (fun i => (hM.eigenvalues i : ℂ)) : Matrix n n ℂ) - (c : ℂ) • 1).PosSemidef := by
    convert hd using 1
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]
  have hp := hd'.mul_mul_conjTranspose_same (hM.eigenvectorUnitary : Matrix n n ℂ)
  have he :
      conjStarAlgAut ℂ _ hM.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hM.eigenvalues) - (c : ℂ) • 1) = M - (c : ℂ) • 1 := by
    rw [map_sub, map_smul, map_one, ← hM.spectral_theorem]
  rw [conjStarAlgAut_apply] at he
  simp only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
    Matrix.star_eq_conjTranspose] at he
  rw [he] at hp
  exact hp

theorem eigenvalues_gt_of_shift_posDef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (c : ℝ) (h : (M - (c : ℂ) • 1).PosDef) (i : n) :
    c < hM.eigenvalues i := by
  let x := hM.eigenvectorBasis i
  have hu : star x.ofLp ⬝ᵥ x.ofLp = (1 : ℂ) := by
    simpa only [x, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hM.eigenvectorBasis.inner_eq_one i
  have hx : x.ofLp ≠ 0 := by
    intro hz
    simp [hz] at hu
  have hp := h.re_dotProduct_pos hx
  have he : M *ᵥ x.ofLp = (hM.eigenvalues i : ℂ) • x.ofLp := by
    ext j
    simpa only [x, Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
      RCLike.ofReal_eq_complex_ofReal, smul_eq_mul]
      using congrFun (hM.mulVec_eigenvectorBasis i) j
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, he, hu, smul_eq_mul, mul_one] at hp
  simpa [RCLike.re_eq_complex_re] using hp

theorem exists_eigenvalue_lt_of_shift_not_posSemidef {M : Matrix n n ℂ}
    (hM : M.IsHermitian) (c : ℝ) (h : ¬(M - (c : ℂ) • 1).PosSemidef) :
    ∃ i, hM.eigenvalues i < c := by
  by_contra hn
  apply h
  apply shift_posSemidef_of_eigenvalues hM
  simpa only [not_exists, not_lt] using hn

end LinMajorization
