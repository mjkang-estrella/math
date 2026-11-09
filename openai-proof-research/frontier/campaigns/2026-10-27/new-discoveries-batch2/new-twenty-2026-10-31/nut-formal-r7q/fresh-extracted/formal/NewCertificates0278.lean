import VerifiedDet
namespace Nut8.NewCertificates0278
def C8896 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8896 : C8896.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8896 : ¬ (C8896.det = 0 ∧ ∀ i, C8896.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8896
def C8897 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8897 : C8897.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8897 : ¬ (C8897.det = 0 ∧ ∀ i, C8897.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8897
def C8898 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8898 : C8898.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8898 : ¬ (C8898.det = 0 ∧ ∀ i, C8898.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8898
def C8899 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8899 : C8899.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8899 : ¬ (C8899.det = 0 ∧ ∀ i, C8899.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8899
def C8900 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8900 : C8900.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8900 : ¬ (C8900.det = 0 ∧ ∀ i, C8900.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8900
def C8901 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8901 : C8901.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8901 : ¬ (C8901.det = 0 ∧ ∀ i, C8901.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8901
def C8902 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8902 : C8902.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8902 : ¬ (C8902.det = 0 ∧ ∀ i, C8902.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8902
def C8903 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8903 : C8903.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8903 : ¬ (C8903.det = 0 ∧ ∀ i, C8903.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8903
def C8904 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8904 : C8904.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8904 : ¬ (C8904.det = 0 ∧ ∀ i, C8904.adjugate i i ≠ 0) := by
  intro h
  have := certificate8904
  rw [h.1] at this
  norm_num at this
def C8905 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8905 : C8905.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8905 : ¬ (C8905.det = 0 ∧ ∀ i, C8905.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8905
def C8906 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8906 : C8906.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8906 : ¬ (C8906.det = 0 ∧ ∀ i, C8906.adjugate i i ≠ 0) := by
  intro h
  have := certificate8906
  rw [h.1] at this
  norm_num at this
def C8907 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8907 : C8907.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8907 : ¬ (C8907.det = 0 ∧ ∀ i, C8907.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8907
def C8908 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8908 : C8908.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8908 : ¬ (C8908.det = 0 ∧ ∀ i, C8908.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8908
def C8909 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8909 : C8909.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8909 : ¬ (C8909.det = 0 ∧ ∀ i, C8909.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8909
def C8910 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8910 : C8910.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8910 : ¬ (C8910.det = 0 ∧ ∀ i, C8910.adjugate i i ≠ 0) := by
  intro h
  have := certificate8910
  rw [h.1] at this
  norm_num at this
def C8911 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8911 : C8911.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8911 : ¬ (C8911.det = 0 ∧ ∀ i, C8911.adjugate i i ≠ 0) := by
  intro h
  have := certificate8911
  rw [h.1] at this
  norm_num at this
def C8912 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8912 : C8912.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8912 : ¬ (C8912.det = 0 ∧ ∀ i, C8912.adjugate i i ≠ 0) := by
  intro h
  have := certificate8912
  rw [h.1] at this
  norm_num at this
def C8913 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8913 : C8913.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8913 : ¬ (C8913.det = 0 ∧ ∀ i, C8913.adjugate i i ≠ 0) := by
  intro h
  have := certificate8913
  rw [h.1] at this
  norm_num at this
def C8914 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8914 : C8914.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8914 : ¬ (C8914.det = 0 ∧ ∀ i, C8914.adjugate i i ≠ 0) := by
  intro h
  have := certificate8914
  rw [h.1] at this
  norm_num at this
def C8915 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8915 : C8915.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8915 : ¬ (C8915.det = 0 ∧ ∀ i, C8915.adjugate i i ≠ 0) := by
  intro h
  have := certificate8915
  rw [h.1] at this
  norm_num at this
def C8916 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8916 : C8916.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8916 : ¬ (C8916.det = 0 ∧ ∀ i, C8916.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8916
def C8917 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8917 : C8917.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8917 : ¬ (C8917.det = 0 ∧ ∀ i, C8917.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8917
def C8918 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8918 : C8918.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8918 : ¬ (C8918.det = 0 ∧ ∀ i, C8918.adjugate i i ≠ 0) := by
  intro h
  have := certificate8918
  rw [h.1] at this
  norm_num at this
def C8919 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8919 : C8919.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8919 : ¬ (C8919.det = 0 ∧ ∀ i, C8919.adjugate i i ≠ 0) := by
  intro h
  have := certificate8919
  rw [h.1] at this
  norm_num at this
def C8920 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8920 : C8920.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8920 : ¬ (C8920.det = 0 ∧ ∀ i, C8920.adjugate i i ≠ 0) := by
  intro h
  have := certificate8920
  rw [h.1] at this
  norm_num at this
def C8921 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8921 : C8921.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8921 : ¬ (C8921.det = 0 ∧ ∀ i, C8921.adjugate i i ≠ 0) := by
  intro h
  have := certificate8921
  rw [h.1] at this
  norm_num at this
def C8922 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8922 : C8922.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8922 : ¬ (C8922.det = 0 ∧ ∀ i, C8922.adjugate i i ≠ 0) := by
  intro h
  have := certificate8922
  rw [h.1] at this
  norm_num at this
def C8923 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8923 : C8923.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8923 : ¬ (C8923.det = 0 ∧ ∀ i, C8923.adjugate i i ≠ 0) := by
  intro h
  have := certificate8923
  rw [h.1] at this
  norm_num at this
def C8924 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8924 : C8924.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8924 : ¬ (C8924.det = 0 ∧ ∀ i, C8924.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8924
def C8925 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8925 : C8925.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8925 : ¬ (C8925.det = 0 ∧ ∀ i, C8925.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8925
def C8926 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8926 : C8926.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8926 : ¬ (C8926.det = 0 ∧ ∀ i, C8926.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate8926
def C8927 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8927 : C8927.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8927 : ¬ (C8927.det = 0 ∧ ∀ i, C8927.adjugate i i ≠ 0) := by
  intro h
  have := certificate8927
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0278
