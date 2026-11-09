import Nut
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
namespace Nut8
open Matrix

/-- A symmetric corank-one matrix with a full nullvector has no singular principal minor. -/
theorem principal_minor_ne_zero {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hs : A.IsSymm) (hd : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin A)) = 1)
    (u : Fin (n+1) → ℝ) (hu : A *ᵥ u = 0) (hf : ∀ i, u i ≠ 0) (i : Fin (n+1)) :
    (A.submatrix i.succAbove i.succAbove).det ≠ 0 := by
  intro hz
  obtain ⟨v, hv, hkv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hz
  let w : Fin (n+1) → ℝ := i.insertNth 0 v
  have hwi : w i = 0 := Fin.insertNth_apply_same _ _ _
  have hws (j : Fin n) : w (i.succAbove j) = v j := Fin.insertNth_apply_succAbove _ _ _ _
  have hrow (j : Fin n) : (A *ᵥ w) (i.succAbove j) = 0 := by
    change (∑ k, A (i.succAbove j) k * w k) = 0
    rw [Fin.sum_univ_succAbove _ i]
    have hj := congrFun hkv j
    change (∑ k, A (i.succAbove j) (i.succAbove k) * v k) = 0 at hj
    simpa only [hwi, mul_zero, zero_add, hws] using hj
  have hdot : u ⬝ᵥ (A *ᵥ w) = 0 := by
    have h := Matrix.dotProduct_transpose_mulVec A u w
    rw [hs.eq, hu] at h
    simpa using h
  have hri : (A *ᵥ w) i = 0 := by
    rw [dotProduct, Fin.sum_univ_succAbove _ i] at hdot
    simp only [hrow, mul_zero, Finset.sum_const_zero, add_zero] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left (hf i)
  have hwk : A *ᵥ w = 0 := by
    ext j
    by_cases hji : j = i
    · subst j; exact hri
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
      exact hrow k
  let uk : LinearMap.ker (Matrix.mulVecLin A) := ⟨u,hu⟩
  let wk : LinearMap.ker (Matrix.mulVecLin A) := ⟨w,hwk⟩
  have huk : uk ≠ 0 := by
    intro h
    exact hf i (congrFun (congrArg Subtype.val h) i)
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hd huk wk
  have he := congrArg Subtype.val hc
  have hci : c * u i = 0 := by
    have hi := congrFun he i
    change c * u i = w i at hi
    exact hi.trans hwi
  have hcz : c = 0 := (mul_eq_zero.mp hci).resolve_right (hf i)
  apply hv
  ext j
  change v j = 0
  have hj := congrFun he (i.succAbove j)
  change c * u (i.succAbove j) = w (i.succAbove j) at hj
  simpa only [hcz, zero_mul, hws] using hj.symm

/-- A4, using principal minors rather than a rank-one adjugate factorization. -/
theorem full_kernel_det_adjugate {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hs : A.IsSymm) (hd : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin A)) = 1)
    (u : Fin (n+1) → ℝ) (hu : A *ᵥ u = 0) (hf : ∀ i, u i ≠ 0) :
    A.det = 0 ∧ ∀ i, A.adjugate i i ≠ 0 := by
  constructor
  · apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨u, ?_, hu⟩
    intro hz
    exact hf 0 (congrFun hz 0)
  · intro i
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hm := principal_minor_ne_zero A hs hd u hu hf i
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hm
end Nut8
