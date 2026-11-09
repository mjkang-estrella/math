import VerifiedDet
namespace Nut8.NewCertificates0002
def C64 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate64 : C64.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction64 : ¬ (C64.det = 0 ∧ ∀ i, C64.adjugate i i ≠ 0) := by
  intro h
  have := certificate64
  rw [h.1] at this
  norm_num at this
def C65 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate65 : C65.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction65 : ¬ (C65.det = 0 ∧ ∀ i, C65.adjugate i i ≠ 0) := by
  intro h
  have := certificate65
  rw [h.1] at this
  norm_num at this
def C66 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate66 : C66.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction66 : ¬ (C66.det = 0 ∧ ∀ i, C66.adjugate i i ≠ 0) := by
  intro h
  have := certificate66
  rw [h.1] at this
  norm_num at this
def C67 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate67 : C67.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction67 : ¬ (C67.det = 0 ∧ ∀ i, C67.adjugate i i ≠ 0) := by
  intro h
  have := certificate67
  rw [h.1] at this
  norm_num at this
def C68 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate68 : C68.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction68 : ¬ (C68.det = 0 ∧ ∀ i, C68.adjugate i i ≠ 0) := by
  intro h
  have := certificate68
  rw [h.1] at this
  norm_num at this
def C69 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate69 : C69.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction69 : ¬ (C69.det = 0 ∧ ∀ i, C69.adjugate i i ≠ 0) := by
  intro h
  have := certificate69
  rw [h.1] at this
  norm_num at this
def C70 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate70 : C70.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction70 : ¬ (C70.det = 0 ∧ ∀ i, C70.adjugate i i ≠ 0) := by
  intro h
  have := certificate70
  rw [h.1] at this
  norm_num at this
def C71 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate71 : C71.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction71 : ¬ (C71.det = 0 ∧ ∀ i, C71.adjugate i i ≠ 0) := by
  intro h
  have := certificate71
  rw [h.1] at this
  norm_num at this
def C72 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate72 : C72.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction72 : ¬ (C72.det = 0 ∧ ∀ i, C72.adjugate i i ≠ 0) := by
  intro h
  have := certificate72
  rw [h.1] at this
  norm_num at this
def C73 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate73 : C73.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction73 : ¬ (C73.det = 0 ∧ ∀ i, C73.adjugate i i ≠ 0) := by
  intro h
  have := certificate73
  rw [h.1] at this
  norm_num at this
def C74 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate74 : C74.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction74 : ¬ (C74.det = 0 ∧ ∀ i, C74.adjugate i i ≠ 0) := by
  intro h
  have := certificate74
  rw [h.1] at this
  norm_num at this
def C75 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate75 : C75.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction75 : ¬ (C75.det = 0 ∧ ∀ i, C75.adjugate i i ≠ 0) := by
  intro h
  have := certificate75
  rw [h.1] at this
  norm_num at this
def C76 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate76 : C76.det = (80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction76 : ¬ (C76.det = 0 ∧ ∀ i, C76.adjugate i i ≠ 0) := by
  intro h
  have := certificate76
  rw [h.1] at this
  norm_num at this
def C77 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate77 : C77.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction77 : ¬ (C77.det = 0 ∧ ∀ i, C77.adjugate i i ≠ 0) := by
  intro h
  have := certificate77
  rw [h.1] at this
  norm_num at this
def C78 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate78 : C78.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction78 : ¬ (C78.det = 0 ∧ ∀ i, C78.adjugate i i ≠ 0) := by
  intro h
  have := certificate78
  rw [h.1] at this
  norm_num at this
def C79 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate79 : C79.det = (-48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction79 : ¬ (C79.det = 0 ∧ ∀ i, C79.adjugate i i ≠ 0) := by
  intro h
  have := certificate79
  rw [h.1] at this
  norm_num at this
def C80 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate80 : C80.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction80 : ¬ (C80.det = 0 ∧ ∀ i, C80.adjugate i i ≠ 0) := by
  intro h
  have := certificate80
  rw [h.1] at this
  norm_num at this
def C81 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate81 : C81.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction81 : ¬ (C81.det = 0 ∧ ∀ i, C81.adjugate i i ≠ 0) := by
  intro h
  have := certificate81
  rw [h.1] at this
  norm_num at this
def C82 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate82 : C82.det = (-80 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction82 : ¬ (C82.det = 0 ∧ ∀ i, C82.adjugate i i ≠ 0) := by
  intro h
  have := certificate82
  rw [h.1] at this
  norm_num at this
def C83 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate83 : C83.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction83 : ¬ (C83.det = 0 ∧ ∀ i, C83.adjugate i i ≠ 0) := by
  intro h
  have := certificate83
  rw [h.1] at this
  norm_num at this
def C84 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate84 : C84.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction84 : ¬ (C84.det = 0 ∧ ∀ i, C84.adjugate i i ≠ 0) := by
  intro h
  have := certificate84
  rw [h.1] at this
  norm_num at this
def C85 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate85 : C85.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction85 : ¬ (C85.det = 0 ∧ ∀ i, C85.adjugate i i ≠ 0) := by
  intro h
  have := certificate85
  rw [h.1] at this
  norm_num at this
def C86 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate86 : C86.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction86 : ¬ (C86.det = 0 ∧ ∀ i, C86.adjugate i i ≠ 0) := by
  intro h
  have := certificate86
  rw [h.1] at this
  norm_num at this
def C87 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate87 : C87.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction87 : ¬ (C87.det = 0 ∧ ∀ i, C87.adjugate i i ≠ 0) := by
  intro h
  have := certificate87
  rw [h.1] at this
  norm_num at this
def C88 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate88 : C88.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction88 : ¬ (C88.det = 0 ∧ ∀ i, C88.adjugate i i ≠ 0) := by
  intro h
  have := certificate88
  rw [h.1] at this
  norm_num at this
def C89 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate89 : C89.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction89 : ¬ (C89.det = 0 ∧ ∀ i, C89.adjugate i i ≠ 0) := by
  intro h
  have := certificate89
  rw [h.1] at this
  norm_num at this
def C90 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate90 : C90.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction90 : ¬ (C90.det = 0 ∧ ∀ i, C90.adjugate i i ≠ 0) := by
  intro h
  have := certificate90
  rw [h.1] at this
  norm_num at this
def C91 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate91 : C91.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction91 : ¬ (C91.det = 0 ∧ ∀ i, C91.adjugate i i ≠ 0) := by
  intro h
  have := certificate91
  rw [h.1] at this
  norm_num at this
def C92 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate92 : C92.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction92 : ¬ (C92.det = 0 ∧ ∀ i, C92.adjugate i i ≠ 0) := by
  intro h
  have := certificate92
  rw [h.1] at this
  norm_num at this
def C93 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate93 : C93.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction93 : ¬ (C93.det = 0 ∧ ∀ i, C93.adjugate i i ≠ 0) := by
  intro h
  have := certificate93
  rw [h.1] at this
  norm_num at this
def C94 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate94 : C94.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction94 : ¬ (C94.det = 0 ∧ ∀ i, C94.adjugate i i ≠ 0) := by
  intro h
  have := certificate94
  rw [h.1] at this
  norm_num at this
def C95 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate95 : C95.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction95 : ¬ (C95.det = 0 ∧ ∀ i, C95.adjugate i i ≠ 0) := by
  intro h
  have := certificate95
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0002
