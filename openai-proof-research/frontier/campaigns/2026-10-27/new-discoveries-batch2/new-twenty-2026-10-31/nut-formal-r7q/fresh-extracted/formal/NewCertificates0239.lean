import VerifiedDet
namespace Nut8.NewCertificates0239
def C7648 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7648 : C7648.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7648 : ¬ (C7648.det = 0 ∧ ∀ i, C7648.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7648
def C7649 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7649 : C7649.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7649 : ¬ (C7649.det = 0 ∧ ∀ i, C7649.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7649
def C7650 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7650 : C7650.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7650 : ¬ (C7650.det = 0 ∧ ∀ i, C7650.adjugate i i ≠ 0) := by
  intro h
  have := certificate7650
  rw [h.1] at this
  norm_num at this
def C7651 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7651 : C7651.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7651 : ¬ (C7651.det = 0 ∧ ∀ i, C7651.adjugate i i ≠ 0) := by
  intro h
  have := certificate7651
  rw [h.1] at this
  norm_num at this
def C7652 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7652 : C7652.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7652 : ¬ (C7652.det = 0 ∧ ∀ i, C7652.adjugate i i ≠ 0) := by
  intro h
  have := certificate7652
  rw [h.1] at this
  norm_num at this
def C7653 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7653 : C7653.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7653 : ¬ (C7653.det = 0 ∧ ∀ i, C7653.adjugate i i ≠ 0) := by
  intro h
  have := certificate7653
  rw [h.1] at this
  norm_num at this
def C7654 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7654 : C7654.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7654 : ¬ (C7654.det = 0 ∧ ∀ i, C7654.adjugate i i ≠ 0) := by
  intro h
  have := certificate7654
  rw [h.1] at this
  norm_num at this
def C7655 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7655 : C7655.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7655 : ¬ (C7655.det = 0 ∧ ∀ i, C7655.adjugate i i ≠ 0) := by
  intro h
  have := certificate7655
  rw [h.1] at this
  norm_num at this
def C7656 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7656 : C7656.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7656 : ¬ (C7656.det = 0 ∧ ∀ i, C7656.adjugate i i ≠ 0) := by
  intro h
  have := certificate7656
  rw [h.1] at this
  norm_num at this
def C7657 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7657 : C7657.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7657 : ¬ (C7657.det = 0 ∧ ∀ i, C7657.adjugate i i ≠ 0) := by
  intro h
  have := certificate7657
  rw [h.1] at this
  norm_num at this
def C7658 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7658 : C7658.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7658 : ¬ (C7658.det = 0 ∧ ∀ i, C7658.adjugate i i ≠ 0) := by
  intro h
  have := certificate7658
  rw [h.1] at this
  norm_num at this
def C7659 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7659 : C7659.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7659 : ¬ (C7659.det = 0 ∧ ∀ i, C7659.adjugate i i ≠ 0) := by
  intro h
  have := certificate7659
  rw [h.1] at this
  norm_num at this
def C7660 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7660 : C7660.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7660 : ¬ (C7660.det = 0 ∧ ∀ i, C7660.adjugate i i ≠ 0) := by
  intro h
  have := certificate7660
  rw [h.1] at this
  norm_num at this
def C7661 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7661 : C7661.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7661 : ¬ (C7661.det = 0 ∧ ∀ i, C7661.adjugate i i ≠ 0) := by
  intro h
  have := certificate7661
  rw [h.1] at this
  norm_num at this
def C7662 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7662 : C7662.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7662 : ¬ (C7662.det = 0 ∧ ∀ i, C7662.adjugate i i ≠ 0) := by
  intro h
  have := certificate7662
  rw [h.1] at this
  norm_num at this
def C7663 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7663 : C7663.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7663 : ¬ (C7663.det = 0 ∧ ∀ i, C7663.adjugate i i ≠ 0) := by
  intro h
  have := certificate7663
  rw [h.1] at this
  norm_num at this
def C7664 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7664 : C7664.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7664 : ¬ (C7664.det = 0 ∧ ∀ i, C7664.adjugate i i ≠ 0) := by
  intro h
  have := certificate7664
  rw [h.1] at this
  norm_num at this
def C7665 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7665 : C7665.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7665 : ¬ (C7665.det = 0 ∧ ∀ i, C7665.adjugate i i ≠ 0) := by
  intro h
  have := certificate7665
  rw [h.1] at this
  norm_num at this
def C7666 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7666 : C7666.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7666 : ¬ (C7666.det = 0 ∧ ∀ i, C7666.adjugate i i ≠ 0) := by
  intro h
  have := certificate7666
  rw [h.1] at this
  norm_num at this
def C7667 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7667 : C7667.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7667 : ¬ (C7667.det = 0 ∧ ∀ i, C7667.adjugate i i ≠ 0) := by
  intro h
  have := certificate7667
  rw [h.1] at this
  norm_num at this
def C7668 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7668 : C7668.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7668 : ¬ (C7668.det = 0 ∧ ∀ i, C7668.adjugate i i ≠ 0) := by
  intro h
  have := certificate7668
  rw [h.1] at this
  norm_num at this
def C7669 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7669 : C7669.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7669 : ¬ (C7669.det = 0 ∧ ∀ i, C7669.adjugate i i ≠ 0) := by
  intro h
  have := certificate7669
  rw [h.1] at this
  norm_num at this
def C7670 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7670 : C7670.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7670 : ¬ (C7670.det = 0 ∧ ∀ i, C7670.adjugate i i ≠ 0) := by
  intro h
  have := certificate7670
  rw [h.1] at this
  norm_num at this
def C7671 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7671 : C7671.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7671 : ¬ (C7671.det = 0 ∧ ∀ i, C7671.adjugate i i ≠ 0) := by
  intro h
  have := certificate7671
  rw [h.1] at this
  norm_num at this
def C7672 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7672 : C7672.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7672 : ¬ (C7672.det = 0 ∧ ∀ i, C7672.adjugate i i ≠ 0) := by
  intro h
  have := certificate7672
  rw [h.1] at this
  norm_num at this
def C7673 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7673 : C7673.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7673 : ¬ (C7673.det = 0 ∧ ∀ i, C7673.adjugate i i ≠ 0) := by
  intro h
  have := certificate7673
  rw [h.1] at this
  norm_num at this
def C7674 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7674 : C7674.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7674 : ¬ (C7674.det = 0 ∧ ∀ i, C7674.adjugate i i ≠ 0) := by
  intro h
  have := certificate7674
  rw [h.1] at this
  norm_num at this
def C7675 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7675 : C7675.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7675 : ¬ (C7675.det = 0 ∧ ∀ i, C7675.adjugate i i ≠ 0) := by
  intro h
  have := certificate7675
  rw [h.1] at this
  norm_num at this
def C7676 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7676 : C7676.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7676 : ¬ (C7676.det = 0 ∧ ∀ i, C7676.adjugate i i ≠ 0) := by
  intro h
  have := certificate7676
  rw [h.1] at this
  norm_num at this
def C7677 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7677 : C7677.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7677 : ¬ (C7677.det = 0 ∧ ∀ i, C7677.adjugate i i ≠ 0) := by
  intro h
  have := certificate7677
  rw [h.1] at this
  norm_num at this
def C7678 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7678 : C7678.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7678 : ¬ (C7678.det = 0 ∧ ∀ i, C7678.adjugate i i ≠ 0) := by
  intro h
  have := certificate7678
  rw [h.1] at this
  norm_num at this
def C7679 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7679 : C7679.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7679 : ¬ (C7679.det = 0 ∧ ∀ i, C7679.adjugate i i ≠ 0) := by
  intro h
  have := certificate7679
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0239
