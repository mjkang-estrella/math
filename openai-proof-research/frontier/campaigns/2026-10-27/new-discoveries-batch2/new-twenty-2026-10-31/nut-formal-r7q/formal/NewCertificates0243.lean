import VerifiedDet
namespace Nut8.NewCertificates0243
def C7776 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7776 : C7776.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7776 : ¬ (C7776.det = 0 ∧ ∀ i, C7776.adjugate i i ≠ 0) := by
  intro h
  have := certificate7776
  rw [h.1] at this
  norm_num at this
def C7777 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7777 : C7777.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7777 : ¬ (C7777.det = 0 ∧ ∀ i, C7777.adjugate i i ≠ 0) := by
  intro h
  have := certificate7777
  rw [h.1] at this
  norm_num at this
def C7778 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7778 : C7778.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7778 : ¬ (C7778.det = 0 ∧ ∀ i, C7778.adjugate i i ≠ 0) := by
  intro h
  have := certificate7778
  rw [h.1] at this
  norm_num at this
def C7779 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 1, -1, 0, 0, -1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7779 : C7779.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7779 : ¬ (C7779.det = 0 ∧ ∀ i, C7779.adjugate i i ≠ 0) := by
  intro h
  have := certificate7779
  rw [h.1] at this
  norm_num at this
def C7780 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7780 : C7780.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7780 : ¬ (C7780.det = 0 ∧ ∀ i, C7780.adjugate i i ≠ 0) := by
  intro h
  have := certificate7780
  rw [h.1] at this
  norm_num at this
def C7781 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7781 : C7781.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7781 : ¬ (C7781.det = 0 ∧ ∀ i, C7781.adjugate i i ≠ 0) := by
  intro h
  have := certificate7781
  rw [h.1] at this
  norm_num at this
def C7782 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7782 : C7782.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7782 : ¬ (C7782.det = 0 ∧ ∀ i, C7782.adjugate i i ≠ 0) := by
  intro h
  have := certificate7782
  rw [h.1] at this
  norm_num at this
def C7783 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7783 : C7783.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7783 : ¬ (C7783.det = 0 ∧ ∀ i, C7783.adjugate i i ≠ 0) := by
  intro h
  have := certificate7783
  rw [h.1] at this
  norm_num at this
def C7784 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7784 : C7784.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7784 : ¬ (C7784.det = 0 ∧ ∀ i, C7784.adjugate i i ≠ 0) := by
  intro h
  have := certificate7784
  rw [h.1] at this
  norm_num at this
def C7785 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7785 : C7785.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7785 : ¬ (C7785.det = 0 ∧ ∀ i, C7785.adjugate i i ≠ 0) := by
  intro h
  have := certificate7785
  rw [h.1] at this
  norm_num at this
def C7786 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7786 : C7786.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7786 : ¬ (C7786.det = 0 ∧ ∀ i, C7786.adjugate i i ≠ 0) := by
  intro h
  have := certificate7786
  rw [h.1] at this
  norm_num at this
def C7787 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7787 : C7787.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7787 : ¬ (C7787.det = 0 ∧ ∀ i, C7787.adjugate i i ≠ 0) := by
  intro h
  have := certificate7787
  rw [h.1] at this
  norm_num at this
def C7788 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7788 : C7788.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7788 : ¬ (C7788.det = 0 ∧ ∀ i, C7788.adjugate i i ≠ 0) := by
  intro h
  have := certificate7788
  rw [h.1] at this
  norm_num at this
def C7789 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7789 : C7789.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7789 : ¬ (C7789.det = 0 ∧ ∀ i, C7789.adjugate i i ≠ 0) := by
  intro h
  have := certificate7789
  rw [h.1] at this
  norm_num at this
def C7790 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7790 : C7790.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7790 : ¬ (C7790.det = 0 ∧ ∀ i, C7790.adjugate i i ≠ 0) := by
  intro h
  have := certificate7790
  rw [h.1] at this
  norm_num at this
def C7791 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7791 : C7791.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7791 : ¬ (C7791.det = 0 ∧ ∀ i, C7791.adjugate i i ≠ 0) := by
  intro h
  have := certificate7791
  rw [h.1] at this
  norm_num at this
def C7792 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7792 : C7792.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7792 : ¬ (C7792.det = 0 ∧ ∀ i, C7792.adjugate i i ≠ 0) := by
  intro h
  have := certificate7792
  rw [h.1] at this
  norm_num at this
def C7793 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7793 : C7793.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7793 : ¬ (C7793.det = 0 ∧ ∀ i, C7793.adjugate i i ≠ 0) := by
  intro h
  have := certificate7793
  rw [h.1] at this
  norm_num at this
def C7794 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7794 : C7794.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7794 : ¬ (C7794.det = 0 ∧ ∀ i, C7794.adjugate i i ≠ 0) := by
  intro h
  have := certificate7794
  rw [h.1] at this
  norm_num at this
def C7795 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7795 : C7795.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7795 : ¬ (C7795.det = 0 ∧ ∀ i, C7795.adjugate i i ≠ 0) := by
  intro h
  have := certificate7795
  rw [h.1] at this
  norm_num at this
def C7796 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7796 : C7796.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7796 : ¬ (C7796.det = 0 ∧ ∀ i, C7796.adjugate i i ≠ 0) := by
  intro h
  have := certificate7796
  rw [h.1] at this
  norm_num at this
def C7797 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7797 : C7797.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7797 : ¬ (C7797.det = 0 ∧ ∀ i, C7797.adjugate i i ≠ 0) := by
  intro h
  have := certificate7797
  rw [h.1] at this
  norm_num at this
def C7798 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7798 : C7798.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7798 : ¬ (C7798.det = 0 ∧ ∀ i, C7798.adjugate i i ≠ 0) := by
  intro h
  have := certificate7798
  rw [h.1] at this
  norm_num at this
def C7799 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7799 : C7799.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7799 : ¬ (C7799.det = 0 ∧ ∀ i, C7799.adjugate i i ≠ 0) := by
  intro h
  have := certificate7799
  rw [h.1] at this
  norm_num at this
def C7800 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7800 : C7800.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7800 : ¬ (C7800.det = 0 ∧ ∀ i, C7800.adjugate i i ≠ 0) := by
  intro h
  have := certificate7800
  rw [h.1] at this
  norm_num at this
def C7801 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7801 : C7801.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7801 : ¬ (C7801.det = 0 ∧ ∀ i, C7801.adjugate i i ≠ 0) := by
  intro h
  have := certificate7801
  rw [h.1] at this
  norm_num at this
def C7802 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7802 : C7802.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7802 : ¬ (C7802.det = 0 ∧ ∀ i, C7802.adjugate i i ≠ 0) := by
  intro h
  have := certificate7802
  rw [h.1] at this
  norm_num at this
def C7803 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7803 : C7803.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7803 : ¬ (C7803.det = 0 ∧ ∀ i, C7803.adjugate i i ≠ 0) := by
  intro h
  have := certificate7803
  rw [h.1] at this
  norm_num at this
def C7804 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7804 : C7804.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7804 : ¬ (C7804.det = 0 ∧ ∀ i, C7804.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7804
def C7805 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7805 : C7805.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7805 : ¬ (C7805.det = 0 ∧ ∀ i, C7805.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7805
def C7806 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7806 : C7806.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7806 : ¬ (C7806.det = 0 ∧ ∀ i, C7806.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7806
def C7807 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7807 : C7807.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7807 : ¬ (C7807.det = 0 ∧ ∀ i, C7807.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7807
end Nut8.NewCertificates0243
