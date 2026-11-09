import VerifiedDet
namespace Nut8.NewCertificates0086
def C2752 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2752 : C2752.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2752 : ¬ (C2752.det = 0 ∧ ∀ i, C2752.adjugate i i ≠ 0) := by
  intro h
  have := certificate2752
  rw [h.1] at this
  norm_num at this
def C2753 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2753 : C2753.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2753 : ¬ (C2753.det = 0 ∧ ∀ i, C2753.adjugate i i ≠ 0) := by
  intro h
  have := certificate2753
  rw [h.1] at this
  norm_num at this
def C2754 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2754 : C2754.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2754 : ¬ (C2754.det = 0 ∧ ∀ i, C2754.adjugate i i ≠ 0) := by
  intro h
  have := certificate2754
  rw [h.1] at this
  norm_num at this
def C2755 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2755 : C2755.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2755 : ¬ (C2755.det = 0 ∧ ∀ i, C2755.adjugate i i ≠ 0) := by
  intro h
  have := certificate2755
  rw [h.1] at this
  norm_num at this
def C2756 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2756 : C2756.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2756 : ¬ (C2756.det = 0 ∧ ∀ i, C2756.adjugate i i ≠ 0) := by
  intro h
  have := certificate2756
  rw [h.1] at this
  norm_num at this
def C2757 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2757 : C2757.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2757 : ¬ (C2757.det = 0 ∧ ∀ i, C2757.adjugate i i ≠ 0) := by
  intro h
  have := certificate2757
  rw [h.1] at this
  norm_num at this
def C2758 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2758 : C2758.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2758 : ¬ (C2758.det = 0 ∧ ∀ i, C2758.adjugate i i ≠ 0) := by
  intro h
  have := certificate2758
  rw [h.1] at this
  norm_num at this
def C2759 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2759 : C2759.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2759 : ¬ (C2759.det = 0 ∧ ∀ i, C2759.adjugate i i ≠ 0) := by
  intro h
  have := certificate2759
  rw [h.1] at this
  norm_num at this
def C2760 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2760 : C2760.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2760 : ¬ (C2760.det = 0 ∧ ∀ i, C2760.adjugate i i ≠ 0) := by
  intro h
  have := certificate2760
  rw [h.1] at this
  norm_num at this
def C2761 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2761 : C2761.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2761 : ¬ (C2761.det = 0 ∧ ∀ i, C2761.adjugate i i ≠ 0) := by
  intro h
  have := certificate2761
  rw [h.1] at this
  norm_num at this
def C2762 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2762 : C2762.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2762 : ¬ (C2762.det = 0 ∧ ∀ i, C2762.adjugate i i ≠ 0) := by
  intro h
  have := certificate2762
  rw [h.1] at this
  norm_num at this
def C2763 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2763 : C2763.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2763 : ¬ (C2763.det = 0 ∧ ∀ i, C2763.adjugate i i ≠ 0) := by
  intro h
  have := certificate2763
  rw [h.1] at this
  norm_num at this
def C2764 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2764 : C2764.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2764 : ¬ (C2764.det = 0 ∧ ∀ i, C2764.adjugate i i ≠ 0) := by
  intro h
  have := certificate2764
  rw [h.1] at this
  norm_num at this
def C2765 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2765 : C2765.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2765 : ¬ (C2765.det = 0 ∧ ∀ i, C2765.adjugate i i ≠ 0) := by
  intro h
  have := certificate2765
  rw [h.1] at this
  norm_num at this
def C2766 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2766 : C2766.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2766 : ¬ (C2766.det = 0 ∧ ∀ i, C2766.adjugate i i ≠ 0) := by
  intro h
  have := certificate2766
  rw [h.1] at this
  norm_num at this
def C2767 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2767 : C2767.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2767 : ¬ (C2767.det = 0 ∧ ∀ i, C2767.adjugate i i ≠ 0) := by
  intro h
  have := certificate2767
  rw [h.1] at this
  norm_num at this
def C2768 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2768 : C2768.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2768 : ¬ (C2768.det = 0 ∧ ∀ i, C2768.adjugate i i ≠ 0) := by
  intro h
  have := certificate2768
  rw [h.1] at this
  norm_num at this
def C2769 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2769 : C2769.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2769 : ¬ (C2769.det = 0 ∧ ∀ i, C2769.adjugate i i ≠ 0) := by
  intro h
  have := certificate2769
  rw [h.1] at this
  norm_num at this
def C2770 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2770 : C2770.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2770 : ¬ (C2770.det = 0 ∧ ∀ i, C2770.adjugate i i ≠ 0) := by
  intro h
  have := certificate2770
  rw [h.1] at this
  norm_num at this
def C2771 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2771 : C2771.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2771 : ¬ (C2771.det = 0 ∧ ∀ i, C2771.adjugate i i ≠ 0) := by
  intro h
  have := certificate2771
  rw [h.1] at this
  norm_num at this
def C2772 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2772 : C2772.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2772 : ¬ (C2772.det = 0 ∧ ∀ i, C2772.adjugate i i ≠ 0) := by
  intro h
  have := certificate2772
  rw [h.1] at this
  norm_num at this
def C2773 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate2773 : C2773.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2773 : ¬ (C2773.det = 0 ∧ ∀ i, C2773.adjugate i i ≠ 0) := by
  intro h
  have := certificate2773
  rw [h.1] at this
  norm_num at this
def C2774 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2774 : C2774.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2774 : ¬ (C2774.det = 0 ∧ ∀ i, C2774.adjugate i i ≠ 0) := by
  intro h
  have := certificate2774
  rw [h.1] at this
  norm_num at this
def C2775 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2775 : C2775.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2775 : ¬ (C2775.det = 0 ∧ ∀ i, C2775.adjugate i i ≠ 0) := by
  intro h
  have := certificate2775
  rw [h.1] at this
  norm_num at this
def C2776 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2776 : C2776.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2776 : ¬ (C2776.det = 0 ∧ ∀ i, C2776.adjugate i i ≠ 0) := by
  intro h
  have := certificate2776
  rw [h.1] at this
  norm_num at this
def C2777 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate2777 : C2777.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2777 : ¬ (C2777.det = 0 ∧ ∀ i, C2777.adjugate i i ≠ 0) := by
  intro h
  have := certificate2777
  rw [h.1] at this
  norm_num at this
def C2778 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2778 : C2778.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2778 : ¬ (C2778.det = 0 ∧ ∀ i, C2778.adjugate i i ≠ 0) := by
  intro h
  have := certificate2778
  rw [h.1] at this
  norm_num at this
def C2779 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2779 : C2779.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2779 : ¬ (C2779.det = 0 ∧ ∀ i, C2779.adjugate i i ≠ 0) := by
  intro h
  have := certificate2779
  rw [h.1] at this
  norm_num at this
def C2780 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2780 : C2780.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2780 : ¬ (C2780.det = 0 ∧ ∀ i, C2780.adjugate i i ≠ 0) := by
  intro h
  have := certificate2780
  rw [h.1] at this
  norm_num at this
def C2781 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate2781 : C2781.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2781 : ¬ (C2781.det = 0 ∧ ∀ i, C2781.adjugate i i ≠ 0) := by
  intro h
  have := certificate2781
  rw [h.1] at this
  norm_num at this
def C2782 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2782 : C2782.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2782 : ¬ (C2782.det = 0 ∧ ∀ i, C2782.adjugate i i ≠ 0) := by
  intro h
  have := certificate2782
  rw [h.1] at this
  norm_num at this
def C2783 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate2783 : C2783.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2783 : ¬ (C2783.det = 0 ∧ ∀ i, C2783.adjugate i i ≠ 0) := by
  intro h
  have := certificate2783
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0086
