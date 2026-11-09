import VerifiedDet
namespace Nut8.NewCertificates0172
def C5504 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5504 : C5504.det = (132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5504 : ¬ (C5504.det = 0 ∧ ∀ i, C5504.adjugate i i ≠ 0) := by
  intro h
  have := certificate5504
  rw [h.1] at this
  norm_num at this
def C5505 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5505 : C5505.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5505 : ¬ (C5505.det = 0 ∧ ∀ i, C5505.adjugate i i ≠ 0) := by
  intro h
  have := certificate5505
  rw [h.1] at this
  norm_num at this
def C5506 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5506 : C5506.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5506 : ¬ (C5506.det = 0 ∧ ∀ i, C5506.adjugate i i ≠ 0) := by
  intro h
  have := certificate5506
  rw [h.1] at this
  norm_num at this
def C5507 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5507 : C5507.det = (132 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5507 : ¬ (C5507.det = 0 ∧ ∀ i, C5507.adjugate i i ≠ 0) := by
  intro h
  have := certificate5507
  rw [h.1] at this
  norm_num at this
def C5508 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5508 : C5508.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5508 : ¬ (C5508.det = 0 ∧ ∀ i, C5508.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5508
def C5509 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5509 : C5509.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5509 : ¬ (C5509.det = 0 ∧ ∀ i, C5509.adjugate i i ≠ 0) := by
  intro h
  have := certificate5509
  rw [h.1] at this
  norm_num at this
def C5510 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5510 : C5510.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5510 : ¬ (C5510.det = 0 ∧ ∀ i, C5510.adjugate i i ≠ 0) := by
  intro h
  have := certificate5510
  rw [h.1] at this
  norm_num at this
def C5511 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5511 : C5511.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5511 : ¬ (C5511.det = 0 ∧ ∀ i, C5511.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5511
def C5512 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5512 : C5512.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5512 : ¬ (C5512.det = 0 ∧ ∀ i, C5512.adjugate i i ≠ 0) := by
  intro h
  have := certificate5512
  rw [h.1] at this
  norm_num at this
def C5513 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5513 : C5513.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5513 : ¬ (C5513.det = 0 ∧ ∀ i, C5513.adjugate i i ≠ 0) := by
  intro h
  have := certificate5513
  rw [h.1] at this
  norm_num at this
def C5514 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5514 : C5514.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5514 : ¬ (C5514.det = 0 ∧ ∀ i, C5514.adjugate i i ≠ 0) := by
  intro h
  have := certificate5514
  rw [h.1] at this
  norm_num at this
def C5515 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5515 : C5515.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5515 : ¬ (C5515.det = 0 ∧ ∀ i, C5515.adjugate i i ≠ 0) := by
  intro h
  have := certificate5515
  rw [h.1] at this
  norm_num at this
def C5516 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5516 : C5516.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5516 : ¬ (C5516.det = 0 ∧ ∀ i, C5516.adjugate i i ≠ 0) := by
  intro h
  have := certificate5516
  rw [h.1] at this
  norm_num at this
def C5517 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5517 : C5517.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5517 : ¬ (C5517.det = 0 ∧ ∀ i, C5517.adjugate i i ≠ 0) := by
  intro h
  have := certificate5517
  rw [h.1] at this
  norm_num at this
def C5518 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5518 : C5518.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5518 : ¬ (C5518.det = 0 ∧ ∀ i, C5518.adjugate i i ≠ 0) := by
  intro h
  have := certificate5518
  rw [h.1] at this
  norm_num at this
def C5519 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5519 : C5519.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5519 : ¬ (C5519.det = 0 ∧ ∀ i, C5519.adjugate i i ≠ 0) := by
  intro h
  have := certificate5519
  rw [h.1] at this
  norm_num at this
def C5520 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5520 : C5520.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5520 : ¬ (C5520.det = 0 ∧ ∀ i, C5520.adjugate i i ≠ 0) := by
  intro h
  have := certificate5520
  rw [h.1] at this
  norm_num at this
def C5521 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5521 : C5521.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5521 : ¬ (C5521.det = 0 ∧ ∀ i, C5521.adjugate i i ≠ 0) := by
  intro h
  have := certificate5521
  rw [h.1] at this
  norm_num at this
def C5522 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5522 : C5522.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5522 : ¬ (C5522.det = 0 ∧ ∀ i, C5522.adjugate i i ≠ 0) := by
  intro h
  have := certificate5522
  rw [h.1] at this
  norm_num at this
def C5523 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5523 : C5523.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5523 : ¬ (C5523.det = 0 ∧ ∀ i, C5523.adjugate i i ≠ 0) := by
  intro h
  have := certificate5523
  rw [h.1] at this
  norm_num at this
def C5524 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5524 : C5524.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5524 : ¬ (C5524.det = 0 ∧ ∀ i, C5524.adjugate i i ≠ 0) := by
  intro h
  have := certificate5524
  rw [h.1] at this
  norm_num at this
def C5525 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5525 : C5525.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5525 : ¬ (C5525.det = 0 ∧ ∀ i, C5525.adjugate i i ≠ 0) := by
  intro h
  have := certificate5525
  rw [h.1] at this
  norm_num at this
def C5526 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5526 : C5526.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5526 : ¬ (C5526.det = 0 ∧ ∀ i, C5526.adjugate i i ≠ 0) := by
  intro h
  have := certificate5526
  rw [h.1] at this
  norm_num at this
def C5527 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5527 : C5527.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5527 : ¬ (C5527.det = 0 ∧ ∀ i, C5527.adjugate i i ≠ 0) := by
  intro h
  have := certificate5527
  rw [h.1] at this
  norm_num at this
def C5528 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5528 : C5528.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5528 : ¬ (C5528.det = 0 ∧ ∀ i, C5528.adjugate i i ≠ 0) := by
  intro h
  have := certificate5528
  rw [h.1] at this
  norm_num at this
def C5529 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5529 : C5529.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5529 : ¬ (C5529.det = 0 ∧ ∀ i, C5529.adjugate i i ≠ 0) := by
  intro h
  have := certificate5529
  rw [h.1] at this
  norm_num at this
def C5530 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5530 : C5530.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5530 : ¬ (C5530.det = 0 ∧ ∀ i, C5530.adjugate i i ≠ 0) := by
  intro h
  have := certificate5530
  rw [h.1] at this
  norm_num at this
def C5531 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5531 : C5531.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5531 : ¬ (C5531.det = 0 ∧ ∀ i, C5531.adjugate i i ≠ 0) := by
  intro h
  have := certificate5531
  rw [h.1] at this
  norm_num at this
def C5532 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5532 : C5532.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5532 : ¬ (C5532.det = 0 ∧ ∀ i, C5532.adjugate i i ≠ 0) := by
  intro h
  have := certificate5532
  rw [h.1] at this
  norm_num at this
def C5533 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5533 : C5533.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5533 : ¬ (C5533.det = 0 ∧ ∀ i, C5533.adjugate i i ≠ 0) := by
  intro h
  have := certificate5533
  rw [h.1] at this
  norm_num at this
def C5534 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5534 : C5534.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5534 : ¬ (C5534.det = 0 ∧ ∀ i, C5534.adjugate i i ≠ 0) := by
  intro h
  have := certificate5534
  rw [h.1] at this
  norm_num at this
def C5535 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5535 : C5535.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5535 : ¬ (C5535.det = 0 ∧ ∀ i, C5535.adjugate i i ≠ 0) := by
  intro h
  have := certificate5535
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0172
