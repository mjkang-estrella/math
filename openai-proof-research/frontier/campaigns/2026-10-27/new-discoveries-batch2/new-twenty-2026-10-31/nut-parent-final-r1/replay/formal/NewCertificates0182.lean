import VerifiedDet
namespace Nut8.NewCertificates0182
def C5824 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5824 : C5824.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5824 : ¬ (C5824.det = 0 ∧ ∀ i, C5824.adjugate i i ≠ 0) := by
  intro h
  have := certificate5824
  rw [h.1] at this
  norm_num at this
def C5825 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5825 : C5825.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5825 : ¬ (C5825.det = 0 ∧ ∀ i, C5825.adjugate i i ≠ 0) := by
  intro h
  have := certificate5825
  rw [h.1] at this
  norm_num at this
def C5826 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5826 : C5826.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5826 : ¬ (C5826.det = 0 ∧ ∀ i, C5826.adjugate i i ≠ 0) := by
  intro h
  have := certificate5826
  rw [h.1] at this
  norm_num at this
def C5827 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5827 : C5827.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5827 : ¬ (C5827.det = 0 ∧ ∀ i, C5827.adjugate i i ≠ 0) := by
  intro h
  have := certificate5827
  rw [h.1] at this
  norm_num at this
def C5828 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5828 : C5828.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5828 : ¬ (C5828.det = 0 ∧ ∀ i, C5828.adjugate i i ≠ 0) := by
  intro h
  have := certificate5828
  rw [h.1] at this
  norm_num at this
def C5829 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5829 : C5829.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5829 : ¬ (C5829.det = 0 ∧ ∀ i, C5829.adjugate i i ≠ 0) := by
  intro h
  have := certificate5829
  rw [h.1] at this
  norm_num at this
def C5830 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5830 : C5830.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5830 : ¬ (C5830.det = 0 ∧ ∀ i, C5830.adjugate i i ≠ 0) := by
  intro h
  have := certificate5830
  rw [h.1] at this
  norm_num at this
def C5831 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5831 : C5831.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5831 : ¬ (C5831.det = 0 ∧ ∀ i, C5831.adjugate i i ≠ 0) := by
  intro h
  have := certificate5831
  rw [h.1] at this
  norm_num at this
def C5832 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5832 : C5832.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5832 : ¬ (C5832.det = 0 ∧ ∀ i, C5832.adjugate i i ≠ 0) := by
  intro h
  have := certificate5832
  rw [h.1] at this
  norm_num at this
def C5833 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5833 : C5833.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5833 : ¬ (C5833.det = 0 ∧ ∀ i, C5833.adjugate i i ≠ 0) := by
  intro h
  have := certificate5833
  rw [h.1] at this
  norm_num at this
def C5834 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5834 : C5834.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5834 : ¬ (C5834.det = 0 ∧ ∀ i, C5834.adjugate i i ≠ 0) := by
  intro h
  have := certificate5834
  rw [h.1] at this
  norm_num at this
def C5835 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5835 : C5835.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5835 : ¬ (C5835.det = 0 ∧ ∀ i, C5835.adjugate i i ≠ 0) := by
  intro h
  have := certificate5835
  rw [h.1] at this
  norm_num at this
def C5836 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5836 : C5836.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5836 : ¬ (C5836.det = 0 ∧ ∀ i, C5836.adjugate i i ≠ 0) := by
  intro h
  have := certificate5836
  rw [h.1] at this
  norm_num at this
def C5837 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5837 : C5837.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5837 : ¬ (C5837.det = 0 ∧ ∀ i, C5837.adjugate i i ≠ 0) := by
  intro h
  have := certificate5837
  rw [h.1] at this
  norm_num at this
def C5838 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5838 : C5838.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5838 : ¬ (C5838.det = 0 ∧ ∀ i, C5838.adjugate i i ≠ 0) := by
  intro h
  have := certificate5838
  rw [h.1] at this
  norm_num at this
def C5839 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5839 : C5839.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5839 : ¬ (C5839.det = 0 ∧ ∀ i, C5839.adjugate i i ≠ 0) := by
  intro h
  have := certificate5839
  rw [h.1] at this
  norm_num at this
def C5840 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5840 : C5840.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5840 : ¬ (C5840.det = 0 ∧ ∀ i, C5840.adjugate i i ≠ 0) := by
  intro h
  have := certificate5840
  rw [h.1] at this
  norm_num at this
def C5841 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5841 : C5841.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5841 : ¬ (C5841.det = 0 ∧ ∀ i, C5841.adjugate i i ≠ 0) := by
  intro h
  have := certificate5841
  rw [h.1] at this
  norm_num at this
def C5842 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5842 : C5842.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5842 : ¬ (C5842.det = 0 ∧ ∀ i, C5842.adjugate i i ≠ 0) := by
  intro h
  have := certificate5842
  rw [h.1] at this
  norm_num at this
def C5843 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5843 : C5843.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5843 : ¬ (C5843.det = 0 ∧ ∀ i, C5843.adjugate i i ≠ 0) := by
  intro h
  have := certificate5843
  rw [h.1] at this
  norm_num at this
def C5844 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5844 : C5844.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5844 : ¬ (C5844.det = 0 ∧ ∀ i, C5844.adjugate i i ≠ 0) := by
  intro h
  have := certificate5844
  rw [h.1] at this
  norm_num at this
def C5845 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5845 : C5845.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5845 : ¬ (C5845.det = 0 ∧ ∀ i, C5845.adjugate i i ≠ 0) := by
  intro h
  have := certificate5845
  rw [h.1] at this
  norm_num at this
def C5846 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5846 : C5846.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5846 : ¬ (C5846.det = 0 ∧ ∀ i, C5846.adjugate i i ≠ 0) := by
  intro h
  have := certificate5846
  rw [h.1] at this
  norm_num at this
def C5847 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5847 : C5847.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5847 : ¬ (C5847.det = 0 ∧ ∀ i, C5847.adjugate i i ≠ 0) := by
  intro h
  have := certificate5847
  rw [h.1] at this
  norm_num at this
def C5848 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5848 : C5848.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5848 : ¬ (C5848.det = 0 ∧ ∀ i, C5848.adjugate i i ≠ 0) := by
  intro h
  have := certificate5848
  rw [h.1] at this
  norm_num at this
def C5849 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5849 : C5849.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5849 : ¬ (C5849.det = 0 ∧ ∀ i, C5849.adjugate i i ≠ 0) := by
  intro h
  have := certificate5849
  rw [h.1] at this
  norm_num at this
def C5850 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5850 : C5850.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5850 : ¬ (C5850.det = 0 ∧ ∀ i, C5850.adjugate i i ≠ 0) := by
  intro h
  have := certificate5850
  rw [h.1] at this
  norm_num at this
def C5851 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5851 : C5851.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5851 : ¬ (C5851.det = 0 ∧ ∀ i, C5851.adjugate i i ≠ 0) := by
  intro h
  have := certificate5851
  rw [h.1] at this
  norm_num at this
def C5852 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5852 : C5852.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5852 : ¬ (C5852.det = 0 ∧ ∀ i, C5852.adjugate i i ≠ 0) := by
  intro h
  have := certificate5852
  rw [h.1] at this
  norm_num at this
def C5853 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5853 : C5853.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5853 : ¬ (C5853.det = 0 ∧ ∀ i, C5853.adjugate i i ≠ 0) := by
  intro h
  have := certificate5853
  rw [h.1] at this
  norm_num at this
def C5854 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5854 : C5854.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5854 : ¬ (C5854.det = 0 ∧ ∀ i, C5854.adjugate i i ≠ 0) := by
  intro h
  have := certificate5854
  rw [h.1] at this
  norm_num at this
def C5855 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5855 : C5855.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5855 : ¬ (C5855.det = 0 ∧ ∀ i, C5855.adjugate i i ≠ 0) := by
  intro h
  have := certificate5855
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0182
