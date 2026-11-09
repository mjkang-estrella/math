import VerifiedDet
namespace Nut8.NewCertificates0211
def C6752 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6752 : C6752.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6752 : ¬ (C6752.det = 0 ∧ ∀ i, C6752.adjugate i i ≠ 0) := by
  intro h
  have := certificate6752
  rw [h.1] at this
  norm_num at this
def C6753 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6753 : C6753.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6753 : ¬ (C6753.det = 0 ∧ ∀ i, C6753.adjugate i i ≠ 0) := by
  intro h
  have := certificate6753
  rw [h.1] at this
  norm_num at this
def C6754 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6754 : C6754.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6754 : ¬ (C6754.det = 0 ∧ ∀ i, C6754.adjugate i i ≠ 0) := by
  intro h
  have := certificate6754
  rw [h.1] at this
  norm_num at this
def C6755 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6755 : C6755.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6755 : ¬ (C6755.det = 0 ∧ ∀ i, C6755.adjugate i i ≠ 0) := by
  intro h
  have := certificate6755
  rw [h.1] at this
  norm_num at this
def C6756 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6756 : C6756.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6756 : ¬ (C6756.det = 0 ∧ ∀ i, C6756.adjugate i i ≠ 0) := by
  intro h
  have := certificate6756
  rw [h.1] at this
  norm_num at this
def C6757 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6757 : C6757.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6757 : ¬ (C6757.det = 0 ∧ ∀ i, C6757.adjugate i i ≠ 0) := by
  intro h
  have := certificate6757
  rw [h.1] at this
  norm_num at this
def C6758 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6758 : C6758.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6758 : ¬ (C6758.det = 0 ∧ ∀ i, C6758.adjugate i i ≠ 0) := by
  intro h
  have := certificate6758
  rw [h.1] at this
  norm_num at this
def C6759 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6759 : C6759.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6759 : ¬ (C6759.det = 0 ∧ ∀ i, C6759.adjugate i i ≠ 0) := by
  intro h
  have := certificate6759
  rw [h.1] at this
  norm_num at this
def C6760 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6760 : C6760.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6760 : ¬ (C6760.det = 0 ∧ ∀ i, C6760.adjugate i i ≠ 0) := by
  intro h
  have := certificate6760
  rw [h.1] at this
  norm_num at this
def C6761 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6761 : C6761.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6761 : ¬ (C6761.det = 0 ∧ ∀ i, C6761.adjugate i i ≠ 0) := by
  intro h
  have := certificate6761
  rw [h.1] at this
  norm_num at this
def C6762 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6762 : C6762.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6762 : ¬ (C6762.det = 0 ∧ ∀ i, C6762.adjugate i i ≠ 0) := by
  intro h
  have := certificate6762
  rw [h.1] at this
  norm_num at this
def C6763 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6763 : C6763.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6763 : ¬ (C6763.det = 0 ∧ ∀ i, C6763.adjugate i i ≠ 0) := by
  intro h
  have := certificate6763
  rw [h.1] at this
  norm_num at this
def C6764 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6764 : C6764.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6764 : ¬ (C6764.det = 0 ∧ ∀ i, C6764.adjugate i i ≠ 0) := by
  intro h
  have := certificate6764
  rw [h.1] at this
  norm_num at this
def C6765 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6765 : C6765.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6765 : ¬ (C6765.det = 0 ∧ ∀ i, C6765.adjugate i i ≠ 0) := by
  intro h
  have := certificate6765
  rw [h.1] at this
  norm_num at this
def C6766 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6766 : C6766.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6766 : ¬ (C6766.det = 0 ∧ ∀ i, C6766.adjugate i i ≠ 0) := by
  intro h
  have := certificate6766
  rw [h.1] at this
  norm_num at this
def C6767 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6767 : C6767.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6767 : ¬ (C6767.det = 0 ∧ ∀ i, C6767.adjugate i i ≠ 0) := by
  intro h
  have := certificate6767
  rw [h.1] at this
  norm_num at this
def C6768 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6768 : C6768.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6768 : ¬ (C6768.det = 0 ∧ ∀ i, C6768.adjugate i i ≠ 0) := by
  intro h
  have := certificate6768
  rw [h.1] at this
  norm_num at this
def C6769 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6769 : C6769.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6769 : ¬ (C6769.det = 0 ∧ ∀ i, C6769.adjugate i i ≠ 0) := by
  intro h
  have := certificate6769
  rw [h.1] at this
  norm_num at this
def C6770 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6770 : C6770.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6770 : ¬ (C6770.det = 0 ∧ ∀ i, C6770.adjugate i i ≠ 0) := by
  intro h
  have := certificate6770
  rw [h.1] at this
  norm_num at this
def C6771 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6771 : C6771.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6771 : ¬ (C6771.det = 0 ∧ ∀ i, C6771.adjugate i i ≠ 0) := by
  intro h
  have := certificate6771
  rw [h.1] at this
  norm_num at this
def C6772 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6772 : C6772.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6772 : ¬ (C6772.det = 0 ∧ ∀ i, C6772.adjugate i i ≠ 0) := by
  intro h
  have := certificate6772
  rw [h.1] at this
  norm_num at this
def C6773 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6773 : C6773.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6773 : ¬ (C6773.det = 0 ∧ ∀ i, C6773.adjugate i i ≠ 0) := by
  intro h
  have := certificate6773
  rw [h.1] at this
  norm_num at this
def C6774 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6774 : C6774.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6774 : ¬ (C6774.det = 0 ∧ ∀ i, C6774.adjugate i i ≠ 0) := by
  intro h
  have := certificate6774
  rw [h.1] at this
  norm_num at this
def C6775 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6775 : C6775.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6775 : ¬ (C6775.det = 0 ∧ ∀ i, C6775.adjugate i i ≠ 0) := by
  intro h
  have := certificate6775
  rw [h.1] at this
  norm_num at this
def C6776 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6776 : C6776.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6776 : ¬ (C6776.det = 0 ∧ ∀ i, C6776.adjugate i i ≠ 0) := by
  intro h
  have := certificate6776
  rw [h.1] at this
  norm_num at this
def C6777 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6777 : C6777.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6777 : ¬ (C6777.det = 0 ∧ ∀ i, C6777.adjugate i i ≠ 0) := by
  intro h
  have := certificate6777
  rw [h.1] at this
  norm_num at this
def C6778 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6778 : C6778.det = (56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6778 : ¬ (C6778.det = 0 ∧ ∀ i, C6778.adjugate i i ≠ 0) := by
  intro h
  have := certificate6778
  rw [h.1] at this
  norm_num at this
def C6779 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6779 : C6779.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6779 : ¬ (C6779.det = 0 ∧ ∀ i, C6779.adjugate i i ≠ 0) := by
  intro h
  have := certificate6779
  rw [h.1] at this
  norm_num at this
def C6780 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6780 : C6780.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6780 : ¬ (C6780.det = 0 ∧ ∀ i, C6780.adjugate i i ≠ 0) := by
  intro h
  have := certificate6780
  rw [h.1] at this
  norm_num at this
def C6781 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6781 : C6781.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6781 : ¬ (C6781.det = 0 ∧ ∀ i, C6781.adjugate i i ≠ 0) := by
  intro h
  have := certificate6781
  rw [h.1] at this
  norm_num at this
def C6782 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6782 : C6782.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6782 : ¬ (C6782.det = 0 ∧ ∀ i, C6782.adjugate i i ≠ 0) := by
  intro h
  have := certificate6782
  rw [h.1] at this
  norm_num at this
def C6783 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6783 : C6783.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6783 : ¬ (C6783.det = 0 ∧ ∀ i, C6783.adjugate i i ≠ 0) := by
  intro h
  have := certificate6783
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0211
