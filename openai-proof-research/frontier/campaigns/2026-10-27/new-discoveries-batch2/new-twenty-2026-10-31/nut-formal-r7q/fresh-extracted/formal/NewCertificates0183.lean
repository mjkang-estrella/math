import VerifiedDet
namespace Nut8.NewCertificates0183
def C5856 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5856 : C5856.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5856 : ¬ (C5856.det = 0 ∧ ∀ i, C5856.adjugate i i ≠ 0) := by
  intro h
  have := certificate5856
  rw [h.1] at this
  norm_num at this
def C5857 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5857 : C5857.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5857 : ¬ (C5857.det = 0 ∧ ∀ i, C5857.adjugate i i ≠ 0) := by
  intro h
  have := certificate5857
  rw [h.1] at this
  norm_num at this
def C5858 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5858 : C5858.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5858 : ¬ (C5858.det = 0 ∧ ∀ i, C5858.adjugate i i ≠ 0) := by
  intro h
  have := certificate5858
  rw [h.1] at this
  norm_num at this
def C5859 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, -1, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5859 : C5859.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5859 : ¬ (C5859.det = 0 ∧ ∀ i, C5859.adjugate i i ≠ 0) := by
  intro h
  have := certificate5859
  rw [h.1] at this
  norm_num at this
def C5860 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5860 : C5860.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5860 : ¬ (C5860.det = 0 ∧ ∀ i, C5860.adjugate i i ≠ 0) := by
  intro h
  have := certificate5860
  rw [h.1] at this
  norm_num at this
def C5861 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5861 : C5861.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5861 : ¬ (C5861.det = 0 ∧ ∀ i, C5861.adjugate i i ≠ 0) := by
  intro h
  have := certificate5861
  rw [h.1] at this
  norm_num at this
def C5862 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5862 : C5862.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5862 : ¬ (C5862.det = 0 ∧ ∀ i, C5862.adjugate i i ≠ 0) := by
  intro h
  have := certificate5862
  rw [h.1] at this
  norm_num at this
def C5863 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5863 : C5863.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5863 : ¬ (C5863.det = 0 ∧ ∀ i, C5863.adjugate i i ≠ 0) := by
  intro h
  have := certificate5863
  rw [h.1] at this
  norm_num at this
def C5864 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5864 : C5864.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5864 : ¬ (C5864.det = 0 ∧ ∀ i, C5864.adjugate i i ≠ 0) := by
  intro h
  have := certificate5864
  rw [h.1] at this
  norm_num at this
def C5865 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5865 : C5865.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5865 : ¬ (C5865.det = 0 ∧ ∀ i, C5865.adjugate i i ≠ 0) := by
  intro h
  have := certificate5865
  rw [h.1] at this
  norm_num at this
def C5866 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5866 : C5866.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5866 : ¬ (C5866.det = 0 ∧ ∀ i, C5866.adjugate i i ≠ 0) := by
  intro h
  have := certificate5866
  rw [h.1] at this
  norm_num at this
def C5867 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5867 : C5867.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5867 : ¬ (C5867.det = 0 ∧ ∀ i, C5867.adjugate i i ≠ 0) := by
  intro h
  have := certificate5867
  rw [h.1] at this
  norm_num at this
def C5868 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5868 : C5868.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5868 : ¬ (C5868.det = 0 ∧ ∀ i, C5868.adjugate i i ≠ 0) := by
  intro h
  have := certificate5868
  rw [h.1] at this
  norm_num at this
def C5869 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5869 : C5869.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5869 : ¬ (C5869.det = 0 ∧ ∀ i, C5869.adjugate i i ≠ 0) := by
  intro h
  have := certificate5869
  rw [h.1] at this
  norm_num at this
def C5870 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5870 : C5870.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5870 : ¬ (C5870.det = 0 ∧ ∀ i, C5870.adjugate i i ≠ 0) := by
  intro h
  have := certificate5870
  rw [h.1] at this
  norm_num at this
def C5871 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5871 : C5871.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5871 : ¬ (C5871.det = 0 ∧ ∀ i, C5871.adjugate i i ≠ 0) := by
  intro h
  have := certificate5871
  rw [h.1] at this
  norm_num at this
def C5872 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5872 : C5872.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5872 : ¬ (C5872.det = 0 ∧ ∀ i, C5872.adjugate i i ≠ 0) := by
  intro h
  have := certificate5872
  rw [h.1] at this
  norm_num at this
def C5873 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5873 : C5873.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5873 : ¬ (C5873.det = 0 ∧ ∀ i, C5873.adjugate i i ≠ 0) := by
  intro h
  have := certificate5873
  rw [h.1] at this
  norm_num at this
def C5874 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5874 : C5874.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5874 : ¬ (C5874.det = 0 ∧ ∀ i, C5874.adjugate i i ≠ 0) := by
  intro h
  have := certificate5874
  rw [h.1] at this
  norm_num at this
def C5875 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5875 : C5875.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5875 : ¬ (C5875.det = 0 ∧ ∀ i, C5875.adjugate i i ≠ 0) := by
  intro h
  have := certificate5875
  rw [h.1] at this
  norm_num at this
def C5876 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5876 : C5876.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5876 : ¬ (C5876.det = 0 ∧ ∀ i, C5876.adjugate i i ≠ 0) := by
  intro h
  have := certificate5876
  rw [h.1] at this
  norm_num at this
def C5877 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5877 : C5877.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5877 : ¬ (C5877.det = 0 ∧ ∀ i, C5877.adjugate i i ≠ 0) := by
  intro h
  have := certificate5877
  rw [h.1] at this
  norm_num at this
def C5878 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5878 : C5878.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5878 : ¬ (C5878.det = 0 ∧ ∀ i, C5878.adjugate i i ≠ 0) := by
  intro h
  have := certificate5878
  rw [h.1] at this
  norm_num at this
def C5879 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5879 : C5879.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5879 : ¬ (C5879.det = 0 ∧ ∀ i, C5879.adjugate i i ≠ 0) := by
  intro h
  have := certificate5879
  rw [h.1] at this
  norm_num at this
def C5880 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5880 : C5880.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5880 : ¬ (C5880.det = 0 ∧ ∀ i, C5880.adjugate i i ≠ 0) := by
  intro h
  have := certificate5880
  rw [h.1] at this
  norm_num at this
def C5881 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5881 : C5881.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5881 : ¬ (C5881.det = 0 ∧ ∀ i, C5881.adjugate i i ≠ 0) := by
  intro h
  have := certificate5881
  rw [h.1] at this
  norm_num at this
def C5882 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5882 : C5882.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5882 : ¬ (C5882.det = 0 ∧ ∀ i, C5882.adjugate i i ≠ 0) := by
  intro h
  have := certificate5882
  rw [h.1] at this
  norm_num at this
def C5883 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5883 : C5883.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5883 : ¬ (C5883.det = 0 ∧ ∀ i, C5883.adjugate i i ≠ 0) := by
  intro h
  have := certificate5883
  rw [h.1] at this
  norm_num at this
def C5884 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5884 : C5884.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5884 : ¬ (C5884.det = 0 ∧ ∀ i, C5884.adjugate i i ≠ 0) := by
  intro h
  have := certificate5884
  rw [h.1] at this
  norm_num at this
def C5885 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5885 : C5885.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5885 : ¬ (C5885.det = 0 ∧ ∀ i, C5885.adjugate i i ≠ 0) := by
  intro h
  have := certificate5885
  rw [h.1] at this
  norm_num at this
def C5886 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5886 : C5886.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5886 : ¬ (C5886.det = 0 ∧ ∀ i, C5886.adjugate i i ≠ 0) := by
  intro h
  have := certificate5886
  rw [h.1] at this
  norm_num at this
def C5887 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5887 : C5887.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5887 : ¬ (C5887.det = 0 ∧ ∀ i, C5887.adjugate i i ≠ 0) := by
  intro h
  have := certificate5887
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0183
