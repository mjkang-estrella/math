import VerifiedDet
namespace Nut8.NewCertificates0055
def C1760 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1760 : C1760.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1760 : ¬ (C1760.det = 0 ∧ ∀ i, C1760.adjugate i i ≠ 0) := by
  intro h
  have := certificate1760
  rw [h.1] at this
  norm_num at this
def C1761 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1761 : C1761.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1761 : ¬ (C1761.det = 0 ∧ ∀ i, C1761.adjugate i i ≠ 0) := by
  intro h
  have := certificate1761
  rw [h.1] at this
  norm_num at this
def C1762 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1762 : C1762.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1762 : ¬ (C1762.det = 0 ∧ ∀ i, C1762.adjugate i i ≠ 0) := by
  intro h
  have := certificate1762
  rw [h.1] at this
  norm_num at this
def C1763 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1763 : C1763.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1763 : ¬ (C1763.det = 0 ∧ ∀ i, C1763.adjugate i i ≠ 0) := by
  intro h
  have := certificate1763
  rw [h.1] at this
  norm_num at this
def C1764 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1764 : C1764.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1764 : ¬ (C1764.det = 0 ∧ ∀ i, C1764.adjugate i i ≠ 0) := by
  intro h
  have := certificate1764
  rw [h.1] at this
  norm_num at this
def C1765 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1765 : C1765.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1765 : ¬ (C1765.det = 0 ∧ ∀ i, C1765.adjugate i i ≠ 0) := by
  intro h
  have := certificate1765
  rw [h.1] at this
  norm_num at this
def C1766 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1766 : C1766.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1766 : ¬ (C1766.det = 0 ∧ ∀ i, C1766.adjugate i i ≠ 0) := by
  intro h
  have := certificate1766
  rw [h.1] at this
  norm_num at this
def C1767 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1767 : C1767.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1767 : ¬ (C1767.det = 0 ∧ ∀ i, C1767.adjugate i i ≠ 0) := by
  intro h
  have := certificate1767
  rw [h.1] at this
  norm_num at this
def C1768 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1768 : C1768.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1768 : ¬ (C1768.det = 0 ∧ ∀ i, C1768.adjugate i i ≠ 0) := by
  intro h
  have := certificate1768
  rw [h.1] at this
  norm_num at this
def C1769 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1769 : C1769.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1769 : ¬ (C1769.det = 0 ∧ ∀ i, C1769.adjugate i i ≠ 0) := by
  intro h
  have := certificate1769
  rw [h.1] at this
  norm_num at this
def C1770 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1770 : C1770.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1770 : ¬ (C1770.det = 0 ∧ ∀ i, C1770.adjugate i i ≠ 0) := by
  intro h
  have := certificate1770
  rw [h.1] at this
  norm_num at this
def C1771 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1771 : C1771.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1771 : ¬ (C1771.det = 0 ∧ ∀ i, C1771.adjugate i i ≠ 0) := by
  intro h
  have := certificate1771
  rw [h.1] at this
  norm_num at this
def C1772 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1772 : C1772.det = (-84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1772 : ¬ (C1772.det = 0 ∧ ∀ i, C1772.adjugate i i ≠ 0) := by
  intro h
  have := certificate1772
  rw [h.1] at this
  norm_num at this
def C1773 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1773 : C1773.det = (-84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1773 : ¬ (C1773.det = 0 ∧ ∀ i, C1773.adjugate i i ≠ 0) := by
  intro h
  have := certificate1773
  rw [h.1] at this
  norm_num at this
def C1774 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1774 : C1774.det = (-156 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1774 : ¬ (C1774.det = 0 ∧ ∀ i, C1774.adjugate i i ≠ 0) := by
  intro h
  have := certificate1774
  rw [h.1] at this
  norm_num at this
def C1775 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1775 : C1775.det = (164 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1775 : ¬ (C1775.det = 0 ∧ ∀ i, C1775.adjugate i i ≠ 0) := by
  intro h
  have := certificate1775
  rw [h.1] at this
  norm_num at this
def C1776 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1776 : C1776.det = (164 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1776 : ¬ (C1776.det = 0 ∧ ∀ i, C1776.adjugate i i ≠ 0) := by
  intro h
  have := certificate1776
  rw [h.1] at this
  norm_num at this
def C1777 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1777 : C1777.det = (-156 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1777 : ¬ (C1777.det = 0 ∧ ∀ i, C1777.adjugate i i ≠ 0) := by
  intro h
  have := certificate1777
  rw [h.1] at this
  norm_num at this
def C1778 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1778 : C1778.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1778 : ¬ (C1778.det = 0 ∧ ∀ i, C1778.adjugate i i ≠ 0) := by
  intro h
  have := certificate1778
  rw [h.1] at this
  norm_num at this
def C1779 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1779 : C1779.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1779 : ¬ (C1779.det = 0 ∧ ∀ i, C1779.adjugate i i ≠ 0) := by
  intro h
  have := certificate1779
  rw [h.1] at this
  norm_num at this
def C1780 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1780 : C1780.det = (31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1780 : ¬ (C1780.det = 0 ∧ ∀ i, C1780.adjugate i i ≠ 0) := by
  intro h
  have := certificate1780
  rw [h.1] at this
  norm_num at this
def C1781 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1781 : C1781.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1781 : ¬ (C1781.det = 0 ∧ ∀ i, C1781.adjugate i i ≠ 0) := by
  intro h
  have := certificate1781
  rw [h.1] at this
  norm_num at this
def C1782 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate1782 : C1782.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1782 : ¬ (C1782.det = 0 ∧ ∀ i, C1782.adjugate i i ≠ 0) := by
  intro h
  have := certificate1782
  rw [h.1] at this
  norm_num at this
def C1783 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate1783 : C1783.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1783 : ¬ (C1783.det = 0 ∧ ∀ i, C1783.adjugate i i ≠ 0) := by
  intro h
  have := certificate1783
  rw [h.1] at this
  norm_num at this
def C1784 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1784 : C1784.det = (-120 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1784 : ¬ (C1784.det = 0 ∧ ∀ i, C1784.adjugate i i ≠ 0) := by
  intro h
  have := certificate1784
  rw [h.1] at this
  norm_num at this
def C1785 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1785 : C1785.det = (152 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1785 : ¬ (C1785.det = 0 ∧ ∀ i, C1785.adjugate i i ≠ 0) := by
  intro h
  have := certificate1785
  rw [h.1] at this
  norm_num at this
def C1786 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1786 : C1786.det = (152 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1786 : ¬ (C1786.det = 0 ∧ ∀ i, C1786.adjugate i i ≠ 0) := by
  intro h
  have := certificate1786
  rw [h.1] at this
  norm_num at this
def C1787 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1787 : C1787.det = (-120 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1787 : ¬ (C1787.det = 0 ∧ ∀ i, C1787.adjugate i i ≠ 0) := by
  intro h
  have := certificate1787
  rw [h.1] at this
  norm_num at this
def C1788 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1788 : C1788.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1788 : ¬ (C1788.det = 0 ∧ ∀ i, C1788.adjugate i i ≠ 0) := by
  intro h
  have := certificate1788
  rw [h.1] at this
  norm_num at this
def C1789 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate1789 : C1789.det = (194 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1789 : ¬ (C1789.det = 0 ∧ ∀ i, C1789.adjugate i i ≠ 0) := by
  intro h
  have := certificate1789
  rw [h.1] at this
  norm_num at this
def C1790 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1790 : C1790.det = (194 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1790 : ¬ (C1790.det = 0 ∧ ∀ i, C1790.adjugate i i ≠ 0) := by
  intro h
  have := certificate1790
  rw [h.1] at this
  norm_num at this
def C1791 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate1791 : C1791.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1791 : ¬ (C1791.det = 0 ∧ ∀ i, C1791.adjugate i i ≠ 0) := by
  intro h
  have := certificate1791
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0055
