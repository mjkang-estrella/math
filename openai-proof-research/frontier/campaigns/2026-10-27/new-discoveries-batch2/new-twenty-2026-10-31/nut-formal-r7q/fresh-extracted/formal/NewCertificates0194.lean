import VerifiedDet
namespace Nut8.NewCertificates0194
def C6208 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1]
theorem certificate6208 : C6208.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6208 : ¬ (C6208.det = 0 ∧ ∀ i, C6208.adjugate i i ≠ 0) := by
  intro h
  have := certificate6208
  rw [h.1] at this
  norm_num at this
def C6209 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1]
theorem certificate6209 : C6209.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6209 : ¬ (C6209.det = 0 ∧ ∀ i, C6209.adjugate i i ≠ 0) := by
  intro h
  have := certificate6209
  rw [h.1] at this
  norm_num at this
def C6210 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, 1]
theorem certificate6210 : C6210.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6210 : ¬ (C6210.det = 0 ∧ ∀ i, C6210.adjugate i i ≠ 0) := by
  intro h
  have := certificate6210
  rw [h.1] at this
  norm_num at this
def C6211 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 1, 0, 0, -1, -1]
theorem certificate6211 : C6211.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6211 : ¬ (C6211.det = 0 ∧ ∀ i, C6211.adjugate i i ≠ 0) := by
  intro h
  have := certificate6211
  rw [h.1] at this
  norm_num at this
def C6212 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6212 : C6212.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6212 : ¬ (C6212.det = 0 ∧ ∀ i, C6212.adjugate i i ≠ 0) := by
  intro h
  have := certificate6212
  rw [h.1] at this
  norm_num at this
def C6213 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6213 : C6213.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6213 : ¬ (C6213.det = 0 ∧ ∀ i, C6213.adjugate i i ≠ 0) := by
  intro h
  have := certificate6213
  rw [h.1] at this
  norm_num at this
def C6214 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6214 : C6214.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6214 : ¬ (C6214.det = 0 ∧ ∀ i, C6214.adjugate i i ≠ 0) := by
  intro h
  have := certificate6214
  rw [h.1] at this
  norm_num at this
def C6215 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6215 : C6215.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6215 : ¬ (C6215.det = 0 ∧ ∀ i, C6215.adjugate i i ≠ 0) := by
  intro h
  have := certificate6215
  rw [h.1] at this
  norm_num at this
def C6216 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6216 : C6216.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6216 : ¬ (C6216.det = 0 ∧ ∀ i, C6216.adjugate i i ≠ 0) := by
  intro h
  have := certificate6216
  rw [h.1] at this
  norm_num at this
def C6217 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6217 : C6217.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6217 : ¬ (C6217.det = 0 ∧ ∀ i, C6217.adjugate i i ≠ 0) := by
  intro h
  have := certificate6217
  rw [h.1] at this
  norm_num at this
def C6218 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6218 : C6218.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6218 : ¬ (C6218.det = 0 ∧ ∀ i, C6218.adjugate i i ≠ 0) := by
  intro h
  have := certificate6218
  rw [h.1] at this
  norm_num at this
def C6219 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6219 : C6219.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6219 : ¬ (C6219.det = 0 ∧ ∀ i, C6219.adjugate i i ≠ 0) := by
  intro h
  have := certificate6219
  rw [h.1] at this
  norm_num at this
def C6220 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6220 : C6220.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6220 : ¬ (C6220.det = 0 ∧ ∀ i, C6220.adjugate i i ≠ 0) := by
  intro h
  have := certificate6220
  rw [h.1] at this
  norm_num at this
def C6221 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6221 : C6221.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6221 : ¬ (C6221.det = 0 ∧ ∀ i, C6221.adjugate i i ≠ 0) := by
  intro h
  have := certificate6221
  rw [h.1] at this
  norm_num at this
def C6222 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6222 : C6222.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6222 : ¬ (C6222.det = 0 ∧ ∀ i, C6222.adjugate i i ≠ 0) := by
  intro h
  have := certificate6222
  rw [h.1] at this
  norm_num at this
def C6223 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, 1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6223 : C6223.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6223 : ¬ (C6223.det = 0 ∧ ∀ i, C6223.adjugate i i ≠ 0) := by
  intro h
  have := certificate6223
  rw [h.1] at this
  norm_num at this
def C6224 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6224 : C6224.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6224 : ¬ (C6224.det = 0 ∧ ∀ i, C6224.adjugate i i ≠ 0) := by
  intro h
  have := certificate6224
  rw [h.1] at this
  norm_num at this
def C6225 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0]
theorem certificate6225 : C6225.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6225 : ¬ (C6225.det = 0 ∧ ∀ i, C6225.adjugate i i ≠ 0) := by
  intro h
  have := certificate6225
  rw [h.1] at this
  norm_num at this
def C6226 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6226 : C6226.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6226 : ¬ (C6226.det = 0 ∧ ∀ i, C6226.adjugate i i ≠ 0) := by
  intro h
  have := certificate6226
  rw [h.1] at this
  norm_num at this
def C6227 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, -1; 0, 0, 0, 2, 0, 0, -1, 0]
theorem certificate6227 : C6227.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6227 : ¬ (C6227.det = 0 ∧ ∀ i, C6227.adjugate i i ≠ 0) := by
  intro h
  have := certificate6227
  rw [h.1] at this
  norm_num at this
def C6228 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6228 : C6228.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6228 : ¬ (C6228.det = 0 ∧ ∀ i, C6228.adjugate i i ≠ 0) := by
  intro h
  have := certificate6228
  rw [h.1] at this
  norm_num at this
def C6229 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6229 : C6229.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6229 : ¬ (C6229.det = 0 ∧ ∀ i, C6229.adjugate i i ≠ 0) := by
  intro h
  have := certificate6229
  rw [h.1] at this
  norm_num at this
def C6230 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6230 : C6230.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6230 : ¬ (C6230.det = 0 ∧ ∀ i, C6230.adjugate i i ≠ 0) := by
  intro h
  have := certificate6230
  rw [h.1] at this
  norm_num at this
def C6231 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6231 : C6231.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6231 : ¬ (C6231.det = 0 ∧ ∀ i, C6231.adjugate i i ≠ 0) := by
  intro h
  have := certificate6231
  rw [h.1] at this
  norm_num at this
def C6232 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6232 : C6232.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6232 : ¬ (C6232.det = 0 ∧ ∀ i, C6232.adjugate i i ≠ 0) := by
  intro h
  have := certificate6232
  rw [h.1] at this
  norm_num at this
def C6233 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6233 : C6233.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6233 : ¬ (C6233.det = 0 ∧ ∀ i, C6233.adjugate i i ≠ 0) := by
  intro h
  have := certificate6233
  rw [h.1] at this
  norm_num at this
def C6234 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, 1]
theorem certificate6234 : C6234.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6234 : ¬ (C6234.det = 0 ∧ ∀ i, C6234.adjugate i i ≠ 0) := by
  intro h
  have := certificate6234
  rw [h.1] at this
  norm_num at this
def C6235 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 0, -1]
theorem certificate6235 : C6235.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6235 : ¬ (C6235.det = 0 ∧ ∀ i, C6235.adjugate i i ≠ 0) := by
  intro h
  have := certificate6235
  rw [h.1] at this
  norm_num at this
def C6236 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6236 : C6236.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6236 : ¬ (C6236.det = 0 ∧ ∀ i, C6236.adjugate i i ≠ 0) := by
  intro h
  have := certificate6236
  rw [h.1] at this
  norm_num at this
def C6237 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6237 : C6237.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6237 : ¬ (C6237.det = 0 ∧ ∀ i, C6237.adjugate i i ≠ 0) := by
  intro h
  have := certificate6237
  rw [h.1] at this
  norm_num at this
def C6238 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1]
theorem certificate6238 : C6238.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6238 : ¬ (C6238.det = 0 ∧ ∀ i, C6238.adjugate i i ≠ 0) := by
  intro h
  have := certificate6238
  rw [h.1] at this
  norm_num at this
def C6239 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, 1, 0, 0, -1]
theorem certificate6239 : C6239.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6239 : ¬ (C6239.det = 0 ∧ ∀ i, C6239.adjugate i i ≠ 0) := by
  intro h
  have := certificate6239
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0194
