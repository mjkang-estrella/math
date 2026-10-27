import AbsoluteBridge

open scoped Matrix.Norms.Operator ComplexOrder MatrixOrder
open Matrix
namespace LinMajorization
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem L_entries : L = !![1280349458544173/1156191252552000, -21119165103283/41292544734000, -494208074307/746893574000;
    -21119165103283/41292544734000, 940084195467437/1156191252552000, 27702113449/53349541000;
    -494208074307/746893574000, 27702113449/53349541000, 38120409366731/36130976642250] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [L, A, Q, D, pow_succ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, map_ofNat]

theorem R_entries : R = !![1668580657/1304654400, -18673199/46594800, -262719/842800;
    -18673199/46594800, 5179335797/6523272000, 1061/2408;
    -262719/842800, 1061/2408, 36799879/40770450] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R, A, Q, D, pow_succ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, map_ofNat]

noncomputable def shiftLower : M3 := lower (-591336622891924/824810105038685)
    (-765034099027236/824810105038685) (623838271836949785448/728631412945757320267)
noncomputable def shiftDiagonal : M3 := diagonal
  ![(164962021007737/231238250510400:ℂ),
    16944916580133891169/323325561175164520000,
    314179008540314170194316/35247544601251010367916125]

theorem L_shift_factor : L - (tau:ℂ) • 1 = shiftLower * shiftDiagonal * star shiftLower := by
  rw [L_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tau, shiftLower, shiftDiagonal, lower, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_ofNat]

theorem L_shift_posDef : (L - (tau:ℂ) • 1).PosDef := by
  rw [L_shift_factor]
  apply (lower_isUnit _ _ _).posDef_star_right_conjugate_iff.mpr
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

noncomputable def witnessVector : Fin 3 → ℂ := ![-19/100,-1,37/50]

theorem R_shift_quadratic :
    (star witnessVector ⬝ᵥ ((R - (tau:ℂ) • 1) *ᵥ witnessVector)).re =
      -137006877457/21744240000000 := by
  rw [R_entries]
  norm_num [witnessVector, tau, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Matrix.smul_apply, Matrix.one_apply, map_ofNat, Complex.div_re, Complex.div_im]

theorem R_shift_not_posSemidef : ¬(R - (tau:ℂ) • 1).PosSemidef := by
  intro h
  have hp := h.re_dotProduct_nonneg witnessVector
  simp only [RCLike.re_eq_complex_re] at hp
  rw [R_shift_quadratic] at hp
  norm_num at hp

theorem trace_eq : L.trace = R.trace := by
  rw [L_entries, R_entries]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

theorem L_posSemidef : L.PosSemidef := by
  exact (A_posDef.posSemidef.pow 2).add
    (by simpa only [Matrix.star_eq_conjTranspose] using
      (D_posSemidef : D.PosSemidef).pow 3 |>.mul_mul_conjTranspose_same Q)

end LinMajorization
