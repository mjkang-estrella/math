import VerifiedDet
namespace Nut8.NewCertificates0180
def C5760 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5760 : C5760.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5760 : ¬ (C5760.det = 0 ∧ ∀ i, C5760.adjugate i i ≠ 0) := by
  intro h
  have := certificate5760
  rw [h.1] at this
  norm_num at this
def C5761 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5761 : C5761.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5761 : ¬ (C5761.det = 0 ∧ ∀ i, C5761.adjugate i i ≠ 0) := by
  intro h
  have := certificate5761
  rw [h.1] at this
  norm_num at this
def C5762 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5762 : C5762.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5762 : ¬ (C5762.det = 0 ∧ ∀ i, C5762.adjugate i i ≠ 0) := by
  intro h
  have := certificate5762
  rw [h.1] at this
  norm_num at this
def C5763 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5763 : C5763.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5763 : ¬ (C5763.det = 0 ∧ ∀ i, C5763.adjugate i i ≠ 0) := by
  intro h
  have := certificate5763
  rw [h.1] at this
  norm_num at this
def C5764 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5764 : C5764.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5764 : ¬ (C5764.det = 0 ∧ ∀ i, C5764.adjugate i i ≠ 0) := by
  intro h
  have := certificate5764
  rw [h.1] at this
  norm_num at this
def C5765 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5765 : C5765.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5765 : ¬ (C5765.det = 0 ∧ ∀ i, C5765.adjugate i i ≠ 0) := by
  intro h
  have := certificate5765
  rw [h.1] at this
  norm_num at this
def C5766 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5766 : C5766.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5766 : ¬ (C5766.det = 0 ∧ ∀ i, C5766.adjugate i i ≠ 0) := by
  intro h
  have := certificate5766
  rw [h.1] at this
  norm_num at this
def C5767 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5767 : C5767.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5767 : ¬ (C5767.det = 0 ∧ ∀ i, C5767.adjugate i i ≠ 0) := by
  intro h
  have := certificate5767
  rw [h.1] at this
  norm_num at this
def C5768 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5768 : C5768.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5768 : ¬ (C5768.det = 0 ∧ ∀ i, C5768.adjugate i i ≠ 0) := by
  intro h
  have := certificate5768
  rw [h.1] at this
  norm_num at this
def C5769 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5769 : C5769.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5769 : ¬ (C5769.det = 0 ∧ ∀ i, C5769.adjugate i i ≠ 0) := by
  intro h
  have := certificate5769
  rw [h.1] at this
  norm_num at this
def C5770 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5770 : C5770.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5770 : ¬ (C5770.det = 0 ∧ ∀ i, C5770.adjugate i i ≠ 0) := by
  intro h
  have := certificate5770
  rw [h.1] at this
  norm_num at this
def C5771 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5771 : C5771.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5771 : ¬ (C5771.det = 0 ∧ ∀ i, C5771.adjugate i i ≠ 0) := by
  intro h
  have := certificate5771
  rw [h.1] at this
  norm_num at this
def C5772 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate5772 : C5772.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5772 : ¬ (C5772.det = 0 ∧ ∀ i, C5772.adjugate i i ≠ 0) := by
  intro h
  have := certificate5772
  rw [h.1] at this
  norm_num at this
def C5773 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate5773 : C5773.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5773 : ¬ (C5773.det = 0 ∧ ∀ i, C5773.adjugate i i ≠ 0) := by
  intro h
  have := certificate5773
  rw [h.1] at this
  norm_num at this
def C5774 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate5774 : C5774.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5774 : ¬ (C5774.det = 0 ∧ ∀ i, C5774.adjugate i i ≠ 0) := by
  intro h
  have := certificate5774
  rw [h.1] at this
  norm_num at this
def C5775 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate5775 : C5775.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5775 : ¬ (C5775.det = 0 ∧ ∀ i, C5775.adjugate i i ≠ 0) := by
  intro h
  have := certificate5775
  rw [h.1] at this
  norm_num at this
def C5776 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate5776 : C5776.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5776 : ¬ (C5776.det = 0 ∧ ∀ i, C5776.adjugate i i ≠ 0) := by
  intro h
  have := certificate5776
  rw [h.1] at this
  norm_num at this
def C5777 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate5777 : C5777.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5777 : ¬ (C5777.det = 0 ∧ ∀ i, C5777.adjugate i i ≠ 0) := by
  intro h
  have := certificate5777
  rw [h.1] at this
  norm_num at this
def C5778 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate5778 : C5778.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5778 : ¬ (C5778.det = 0 ∧ ∀ i, C5778.adjugate i i ≠ 0) := by
  intro h
  have := certificate5778
  rw [h.1] at this
  norm_num at this
def C5779 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate5779 : C5779.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5779 : ¬ (C5779.det = 0 ∧ ∀ i, C5779.adjugate i i ≠ 0) := by
  intro h
  have := certificate5779
  rw [h.1] at this
  norm_num at this
def C5780 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate5780 : C5780.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5780 : ¬ (C5780.det = 0 ∧ ∀ i, C5780.adjugate i i ≠ 0) := by
  intro h
  have := certificate5780
  rw [h.1] at this
  norm_num at this
def C5781 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
theorem certificate5781 : C5781.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5781 : ¬ (C5781.det = 0 ∧ ∀ i, C5781.adjugate i i ≠ 0) := by
  intro h
  have := certificate5781
  rw [h.1] at this
  norm_num at this
def C5782 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate5782 : C5782.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5782 : ¬ (C5782.det = 0 ∧ ∀ i, C5782.adjugate i i ≠ 0) := by
  intro h
  have := certificate5782
  rw [h.1] at this
  norm_num at this
def C5783 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 1, -1, 0, 0]
theorem certificate5783 : C5783.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5783 : ¬ (C5783.det = 0 ∧ ∀ i, C5783.adjugate i i ≠ 0) := by
  intro h
  have := certificate5783
  rw [h.1] at this
  norm_num at this
def C5784 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate5784 : C5784.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5784 : ¬ (C5784.det = 0 ∧ ∀ i, C5784.adjugate i i ≠ 0) := by
  intro h
  have := certificate5784
  rw [h.1] at this
  norm_num at this
def C5785 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, -1, 1, 0, 0]
theorem certificate5785 : C5785.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5785 : ¬ (C5785.det = 0 ∧ ∀ i, C5785.adjugate i i ≠ 0) := by
  intro h
  have := certificate5785
  rw [h.1] at this
  norm_num at this
def C5786 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate5786 : C5786.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5786 : ¬ (C5786.det = 0 ∧ ∀ i, C5786.adjugate i i ≠ 0) := by
  intro h
  have := certificate5786
  rw [h.1] at this
  norm_num at this
def C5787 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, -1, -1, 0, 0]
theorem certificate5787 : C5787.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5787 : ¬ (C5787.det = 0 ∧ ∀ i, C5787.adjugate i i ≠ 0) := by
  intro h
  have := certificate5787
  rw [h.1] at this
  norm_num at this
def C5788 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5788 : C5788.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5788 : ¬ (C5788.det = 0 ∧ ∀ i, C5788.adjugate i i ≠ 0) := by
  intro h
  have := certificate5788
  rw [h.1] at this
  norm_num at this
def C5789 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5789 : C5789.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5789 : ¬ (C5789.det = 0 ∧ ∀ i, C5789.adjugate i i ≠ 0) := by
  intro h
  have := certificate5789
  rw [h.1] at this
  norm_num at this
def C5790 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5790 : C5790.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5790 : ¬ (C5790.det = 0 ∧ ∀ i, C5790.adjugate i i ≠ 0) := by
  intro h
  have := certificate5790
  rw [h.1] at this
  norm_num at this
def C5791 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5791 : C5791.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5791 : ¬ (C5791.det = 0 ∧ ∀ i, C5791.adjugate i i ≠ 0) := by
  intro h
  have := certificate5791
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0180
