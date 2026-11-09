import VerifiedDet
namespace Nut8.NewCertificates0241
def C7712 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7712 : C7712.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7712 : ¬ (C7712.det = 0 ∧ ∀ i, C7712.adjugate i i ≠ 0) := by
  intro h
  have := certificate7712
  rw [h.1] at this
  norm_num at this
def C7713 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7713 : C7713.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7713 : ¬ (C7713.det = 0 ∧ ∀ i, C7713.adjugate i i ≠ 0) := by
  intro h
  have := certificate7713
  rw [h.1] at this
  norm_num at this
def C7714 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7714 : C7714.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7714 : ¬ (C7714.det = 0 ∧ ∀ i, C7714.adjugate i i ≠ 0) := by
  intro h
  have := certificate7714
  rw [h.1] at this
  norm_num at this
def C7715 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7715 : C7715.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7715 : ¬ (C7715.det = 0 ∧ ∀ i, C7715.adjugate i i ≠ 0) := by
  intro h
  have := certificate7715
  rw [h.1] at this
  norm_num at this
def C7716 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7716 : C7716.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7716 : ¬ (C7716.det = 0 ∧ ∀ i, C7716.adjugate i i ≠ 0) := by
  intro h
  have := certificate7716
  rw [h.1] at this
  norm_num at this
def C7717 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7717 : C7717.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7717 : ¬ (C7717.det = 0 ∧ ∀ i, C7717.adjugate i i ≠ 0) := by
  intro h
  have := certificate7717
  rw [h.1] at this
  norm_num at this
def C7718 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7718 : C7718.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7718 : ¬ (C7718.det = 0 ∧ ∀ i, C7718.adjugate i i ≠ 0) := by
  intro h
  have := certificate7718
  rw [h.1] at this
  norm_num at this
def C7719 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7719 : C7719.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7719 : ¬ (C7719.det = 0 ∧ ∀ i, C7719.adjugate i i ≠ 0) := by
  intro h
  have := certificate7719
  rw [h.1] at this
  norm_num at this
def C7720 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7720 : C7720.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7720 : ¬ (C7720.det = 0 ∧ ∀ i, C7720.adjugate i i ≠ 0) := by
  intro h
  have := certificate7720
  rw [h.1] at this
  norm_num at this
def C7721 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7721 : C7721.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7721 : ¬ (C7721.det = 0 ∧ ∀ i, C7721.adjugate i i ≠ 0) := by
  intro h
  have := certificate7721
  rw [h.1] at this
  norm_num at this
def C7722 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7722 : C7722.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7722 : ¬ (C7722.det = 0 ∧ ∀ i, C7722.adjugate i i ≠ 0) := by
  intro h
  have := certificate7722
  rw [h.1] at this
  norm_num at this
def C7723 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7723 : C7723.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7723 : ¬ (C7723.det = 0 ∧ ∀ i, C7723.adjugate i i ≠ 0) := by
  intro h
  have := certificate7723
  rw [h.1] at this
  norm_num at this
def C7724 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7724 : C7724.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7724 : ¬ (C7724.det = 0 ∧ ∀ i, C7724.adjugate i i ≠ 0) := by
  intro h
  have := certificate7724
  rw [h.1] at this
  norm_num at this
def C7725 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7725 : C7725.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7725 : ¬ (C7725.det = 0 ∧ ∀ i, C7725.adjugate i i ≠ 0) := by
  intro h
  have := certificate7725
  rw [h.1] at this
  norm_num at this
def C7726 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7726 : C7726.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7726 : ¬ (C7726.det = 0 ∧ ∀ i, C7726.adjugate i i ≠ 0) := by
  intro h
  have := certificate7726
  rw [h.1] at this
  norm_num at this
def C7727 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7727 : C7727.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7727 : ¬ (C7727.det = 0 ∧ ∀ i, C7727.adjugate i i ≠ 0) := by
  intro h
  have := certificate7727
  rw [h.1] at this
  norm_num at this
def C7728 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7728 : C7728.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7728 : ¬ (C7728.det = 0 ∧ ∀ i, C7728.adjugate i i ≠ 0) := by
  intro h
  have := certificate7728
  rw [h.1] at this
  norm_num at this
def C7729 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7729 : C7729.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7729 : ¬ (C7729.det = 0 ∧ ∀ i, C7729.adjugate i i ≠ 0) := by
  intro h
  have := certificate7729
  rw [h.1] at this
  norm_num at this
def C7730 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7730 : C7730.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7730 : ¬ (C7730.det = 0 ∧ ∀ i, C7730.adjugate i i ≠ 0) := by
  intro h
  have := certificate7730
  rw [h.1] at this
  norm_num at this
def C7731 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7731 : C7731.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7731 : ¬ (C7731.det = 0 ∧ ∀ i, C7731.adjugate i i ≠ 0) := by
  intro h
  have := certificate7731
  rw [h.1] at this
  norm_num at this
def C7732 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7732 : C7732.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7732 : ¬ (C7732.det = 0 ∧ ∀ i, C7732.adjugate i i ≠ 0) := by
  intro h
  have := certificate7732
  rw [h.1] at this
  norm_num at this
def C7733 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7733 : C7733.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7733 : ¬ (C7733.det = 0 ∧ ∀ i, C7733.adjugate i i ≠ 0) := by
  intro h
  have := certificate7733
  rw [h.1] at this
  norm_num at this
def C7734 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7734 : C7734.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7734 : ¬ (C7734.det = 0 ∧ ∀ i, C7734.adjugate i i ≠ 0) := by
  intro h
  have := certificate7734
  rw [h.1] at this
  norm_num at this
def C7735 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7735 : C7735.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7735 : ¬ (C7735.det = 0 ∧ ∀ i, C7735.adjugate i i ≠ 0) := by
  intro h
  have := certificate7735
  rw [h.1] at this
  norm_num at this
def C7736 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7736 : C7736.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7736 : ¬ (C7736.det = 0 ∧ ∀ i, C7736.adjugate i i ≠ 0) := by
  intro h
  have := certificate7736
  rw [h.1] at this
  norm_num at this
def C7737 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7737 : C7737.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7737 : ¬ (C7737.det = 0 ∧ ∀ i, C7737.adjugate i i ≠ 0) := by
  intro h
  have := certificate7737
  rw [h.1] at this
  norm_num at this
def C7738 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7738 : C7738.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7738 : ¬ (C7738.det = 0 ∧ ∀ i, C7738.adjugate i i ≠ 0) := by
  intro h
  have := certificate7738
  rw [h.1] at this
  norm_num at this
def C7739 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, -1, 0, 0; 0, 1, 0, 0, -1, 0, 0, -1; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7739 : C7739.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7739 : ¬ (C7739.det = 0 ∧ ∀ i, C7739.adjugate i i ≠ 0) := by
  intro h
  have := certificate7739
  rw [h.1] at this
  norm_num at this
def C7740 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0]
theorem certificate7740 : C7740.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7740 : ¬ (C7740.det = 0 ∧ ∀ i, C7740.adjugate i i ≠ 0) := by
  intro h
  have := certificate7740
  rw [h.1] at this
  norm_num at this
def C7741 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, 1, -1, 0]
theorem certificate7741 : C7741.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7741 : ¬ (C7741.det = 0 ∧ ∀ i, C7741.adjugate i i ≠ 0) := by
  intro h
  have := certificate7741
  rw [h.1] at this
  norm_num at this
def C7742 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, -1, 1, 0]
theorem certificate7742 : C7742.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7742 : ¬ (C7742.det = 0 ∧ ∀ i, C7742.adjugate i i ≠ 0) := by
  intro h
  have := certificate7742
  rw [h.1] at this
  norm_num at this
def C7743 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 1, 0, 0, -1, -1, 0]
theorem certificate7743 : C7743.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7743 : ¬ (C7743.det = 0 ∧ ∀ i, C7743.adjugate i i ≠ 0) := by
  intro h
  have := certificate7743
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0241
