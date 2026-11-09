import VerifiedDet
namespace Nut8.NewCertificates0242
def C7744 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7744 : C7744.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7744 : ¬ (C7744.det = 0 ∧ ∀ i, C7744.adjugate i i ≠ 0) := by
  intro h
  have := certificate7744
  rw [h.1] at this
  norm_num at this
def C7745 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7745 : C7745.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7745 : ¬ (C7745.det = 0 ∧ ∀ i, C7745.adjugate i i ≠ 0) := by
  intro h
  have := certificate7745
  rw [h.1] at this
  norm_num at this
def C7746 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7746 : C7746.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7746 : ¬ (C7746.det = 0 ∧ ∀ i, C7746.adjugate i i ≠ 0) := by
  intro h
  have := certificate7746
  rw [h.1] at this
  norm_num at this
def C7747 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7747 : C7747.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7747 : ¬ (C7747.det = 0 ∧ ∀ i, C7747.adjugate i i ≠ 0) := by
  intro h
  have := certificate7747
  rw [h.1] at this
  norm_num at this
def C7748 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7748 : C7748.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7748 : ¬ (C7748.det = 0 ∧ ∀ i, C7748.adjugate i i ≠ 0) := by
  intro h
  have := certificate7748
  rw [h.1] at this
  norm_num at this
def C7749 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7749 : C7749.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7749 : ¬ (C7749.det = 0 ∧ ∀ i, C7749.adjugate i i ≠ 0) := by
  intro h
  have := certificate7749
  rw [h.1] at this
  norm_num at this
def C7750 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7750 : C7750.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7750 : ¬ (C7750.det = 0 ∧ ∀ i, C7750.adjugate i i ≠ 0) := by
  intro h
  have := certificate7750
  rw [h.1] at this
  norm_num at this
def C7751 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7751 : C7751.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7751 : ¬ (C7751.det = 0 ∧ ∀ i, C7751.adjugate i i ≠ 0) := by
  intro h
  have := certificate7751
  rw [h.1] at this
  norm_num at this
def C7752 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7752 : C7752.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7752 : ¬ (C7752.det = 0 ∧ ∀ i, C7752.adjugate i i ≠ 0) := by
  intro h
  have := certificate7752
  rw [h.1] at this
  norm_num at this
def C7753 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7753 : C7753.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7753 : ¬ (C7753.det = 0 ∧ ∀ i, C7753.adjugate i i ≠ 0) := by
  intro h
  have := certificate7753
  rw [h.1] at this
  norm_num at this
def C7754 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7754 : C7754.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7754 : ¬ (C7754.det = 0 ∧ ∀ i, C7754.adjugate i i ≠ 0) := by
  intro h
  have := certificate7754
  rw [h.1] at this
  norm_num at this
def C7755 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7755 : C7755.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7755 : ¬ (C7755.det = 0 ∧ ∀ i, C7755.adjugate i i ≠ 0) := by
  intro h
  have := certificate7755
  rw [h.1] at this
  norm_num at this
def C7756 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7756 : C7756.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7756 : ¬ (C7756.det = 0 ∧ ∀ i, C7756.adjugate i i ≠ 0) := by
  intro h
  have := certificate7756
  rw [h.1] at this
  norm_num at this
def C7757 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7757 : C7757.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7757 : ¬ (C7757.det = 0 ∧ ∀ i, C7757.adjugate i i ≠ 0) := by
  intro h
  have := certificate7757
  rw [h.1] at this
  norm_num at this
def C7758 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7758 : C7758.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7758 : ¬ (C7758.det = 0 ∧ ∀ i, C7758.adjugate i i ≠ 0) := by
  intro h
  have := certificate7758
  rw [h.1] at this
  norm_num at this
def C7759 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7759 : C7759.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7759 : ¬ (C7759.det = 0 ∧ ∀ i, C7759.adjugate i i ≠ 0) := by
  intro h
  have := certificate7759
  rw [h.1] at this
  norm_num at this
def C7760 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7760 : C7760.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7760 : ¬ (C7760.det = 0 ∧ ∀ i, C7760.adjugate i i ≠ 0) := by
  intro h
  have := certificate7760
  rw [h.1] at this
  norm_num at this
def C7761 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7761 : C7761.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7761 : ¬ (C7761.det = 0 ∧ ∀ i, C7761.adjugate i i ≠ 0) := by
  intro h
  have := certificate7761
  rw [h.1] at this
  norm_num at this
def C7762 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7762 : C7762.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7762 : ¬ (C7762.det = 0 ∧ ∀ i, C7762.adjugate i i ≠ 0) := by
  intro h
  have := certificate7762
  rw [h.1] at this
  norm_num at this
def C7763 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7763 : C7763.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7763 : ¬ (C7763.det = 0 ∧ ∀ i, C7763.adjugate i i ≠ 0) := by
  intro h
  have := certificate7763
  rw [h.1] at this
  norm_num at this
def C7764 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7764 : C7764.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7764 : ¬ (C7764.det = 0 ∧ ∀ i, C7764.adjugate i i ≠ 0) := by
  intro h
  have := certificate7764
  rw [h.1] at this
  norm_num at this
def C7765 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7765 : C7765.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7765 : ¬ (C7765.det = 0 ∧ ∀ i, C7765.adjugate i i ≠ 0) := by
  intro h
  have := certificate7765
  rw [h.1] at this
  norm_num at this
def C7766 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7766 : C7766.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7766 : ¬ (C7766.det = 0 ∧ ∀ i, C7766.adjugate i i ≠ 0) := by
  intro h
  have := certificate7766
  rw [h.1] at this
  norm_num at this
def C7767 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7767 : C7767.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7767 : ¬ (C7767.det = 0 ∧ ∀ i, C7767.adjugate i i ≠ 0) := by
  intro h
  have := certificate7767
  rw [h.1] at this
  norm_num at this
def C7768 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7768 : C7768.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7768 : ¬ (C7768.det = 0 ∧ ∀ i, C7768.adjugate i i ≠ 0) := by
  intro h
  have := certificate7768
  rw [h.1] at this
  norm_num at this
def C7769 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7769 : C7769.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7769 : ¬ (C7769.det = 0 ∧ ∀ i, C7769.adjugate i i ≠ 0) := by
  intro h
  have := certificate7769
  rw [h.1] at this
  norm_num at this
def C7770 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7770 : C7770.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7770 : ¬ (C7770.det = 0 ∧ ∀ i, C7770.adjugate i i ≠ 0) := by
  intro h
  have := certificate7770
  rw [h.1] at this
  norm_num at this
def C7771 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7771 : C7771.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7771 : ¬ (C7771.det = 0 ∧ ∀ i, C7771.adjugate i i ≠ 0) := by
  intro h
  have := certificate7771
  rw [h.1] at this
  norm_num at this
def C7772 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7772 : C7772.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7772 : ¬ (C7772.det = 0 ∧ ∀ i, C7772.adjugate i i ≠ 0) := by
  intro h
  have := certificate7772
  rw [h.1] at this
  norm_num at this
def C7773 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7773 : C7773.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7773 : ¬ (C7773.det = 0 ∧ ∀ i, C7773.adjugate i i ≠ 0) := by
  intro h
  have := certificate7773
  rw [h.1] at this
  norm_num at this
def C7774 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7774 : C7774.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7774 : ¬ (C7774.det = 0 ∧ ∀ i, C7774.adjugate i i ≠ 0) := by
  intro h
  have := certificate7774
  rw [h.1] at this
  norm_num at this
def C7775 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7775 : C7775.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7775 : ¬ (C7775.det = 0 ∧ ∀ i, C7775.adjugate i i ≠ 0) := by
  intro h
  have := certificate7775
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0242
