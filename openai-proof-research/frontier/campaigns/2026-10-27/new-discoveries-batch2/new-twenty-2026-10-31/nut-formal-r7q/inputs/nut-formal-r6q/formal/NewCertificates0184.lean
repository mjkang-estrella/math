import VerifiedDet
namespace Nut8.NewCertificates0184
def C5888 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5888 : C5888.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5888 : ¬ (C5888.det = 0 ∧ ∀ i, C5888.adjugate i i ≠ 0) := by
  intro h
  have := certificate5888
  rw [h.1] at this
  norm_num at this
def C5889 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5889 : C5889.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5889 : ¬ (C5889.det = 0 ∧ ∀ i, C5889.adjugate i i ≠ 0) := by
  intro h
  have := certificate5889
  rw [h.1] at this
  norm_num at this
def C5890 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5890 : C5890.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5890 : ¬ (C5890.det = 0 ∧ ∀ i, C5890.adjugate i i ≠ 0) := by
  intro h
  have := certificate5890
  rw [h.1] at this
  norm_num at this
def C5891 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5891 : C5891.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5891 : ¬ (C5891.det = 0 ∧ ∀ i, C5891.adjugate i i ≠ 0) := by
  intro h
  have := certificate5891
  rw [h.1] at this
  norm_num at this
def C5892 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5892 : C5892.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5892 : ¬ (C5892.det = 0 ∧ ∀ i, C5892.adjugate i i ≠ 0) := by
  intro h
  have := certificate5892
  rw [h.1] at this
  norm_num at this
def C5893 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5893 : C5893.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5893 : ¬ (C5893.det = 0 ∧ ∀ i, C5893.adjugate i i ≠ 0) := by
  intro h
  have := certificate5893
  rw [h.1] at this
  norm_num at this
def C5894 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5894 : C5894.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5894 : ¬ (C5894.det = 0 ∧ ∀ i, C5894.adjugate i i ≠ 0) := by
  intro h
  have := certificate5894
  rw [h.1] at this
  norm_num at this
def C5895 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5895 : C5895.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5895 : ¬ (C5895.det = 0 ∧ ∀ i, C5895.adjugate i i ≠ 0) := by
  intro h
  have := certificate5895
  rw [h.1] at this
  norm_num at this
def C5896 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5896 : C5896.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5896 : ¬ (C5896.det = 0 ∧ ∀ i, C5896.adjugate i i ≠ 0) := by
  intro h
  have := certificate5896
  rw [h.1] at this
  norm_num at this
def C5897 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5897 : C5897.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5897 : ¬ (C5897.det = 0 ∧ ∀ i, C5897.adjugate i i ≠ 0) := by
  intro h
  have := certificate5897
  rw [h.1] at this
  norm_num at this
def C5898 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5898 : C5898.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5898 : ¬ (C5898.det = 0 ∧ ∀ i, C5898.adjugate i i ≠ 0) := by
  intro h
  have := certificate5898
  rw [h.1] at this
  norm_num at this
def C5899 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5899 : C5899.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5899 : ¬ (C5899.det = 0 ∧ ∀ i, C5899.adjugate i i ≠ 0) := by
  intro h
  have := certificate5899
  rw [h.1] at this
  norm_num at this
def C5900 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5900 : C5900.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5900 : ¬ (C5900.det = 0 ∧ ∀ i, C5900.adjugate i i ≠ 0) := by
  intro h
  have := certificate5900
  rw [h.1] at this
  norm_num at this
def C5901 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5901 : C5901.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5901 : ¬ (C5901.det = 0 ∧ ∀ i, C5901.adjugate i i ≠ 0) := by
  intro h
  have := certificate5901
  rw [h.1] at this
  norm_num at this
def C5902 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5902 : C5902.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5902 : ¬ (C5902.det = 0 ∧ ∀ i, C5902.adjugate i i ≠ 0) := by
  intro h
  have := certificate5902
  rw [h.1] at this
  norm_num at this
def C5903 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5903 : C5903.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5903 : ¬ (C5903.det = 0 ∧ ∀ i, C5903.adjugate i i ≠ 0) := by
  intro h
  have := certificate5903
  rw [h.1] at this
  norm_num at this
def C5904 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5904 : C5904.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5904 : ¬ (C5904.det = 0 ∧ ∀ i, C5904.adjugate i i ≠ 0) := by
  intro h
  have := certificate5904
  rw [h.1] at this
  norm_num at this
def C5905 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5905 : C5905.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5905 : ¬ (C5905.det = 0 ∧ ∀ i, C5905.adjugate i i ≠ 0) := by
  intro h
  have := certificate5905
  rw [h.1] at this
  norm_num at this
def C5906 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5906 : C5906.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5906 : ¬ (C5906.det = 0 ∧ ∀ i, C5906.adjugate i i ≠ 0) := by
  intro h
  have := certificate5906
  rw [h.1] at this
  norm_num at this
def C5907 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5907 : C5907.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5907 : ¬ (C5907.det = 0 ∧ ∀ i, C5907.adjugate i i ≠ 0) := by
  intro h
  have := certificate5907
  rw [h.1] at this
  norm_num at this
def C5908 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5908 : C5908.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5908 : ¬ (C5908.det = 0 ∧ ∀ i, C5908.adjugate i i ≠ 0) := by
  intro h
  have := certificate5908
  rw [h.1] at this
  norm_num at this
def C5909 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5909 : C5909.det = (-60 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5909 : ¬ (C5909.det = 0 ∧ ∀ i, C5909.adjugate i i ≠ 0) := by
  intro h
  have := certificate5909
  rw [h.1] at this
  norm_num at this
def C5910 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5910 : C5910.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5910 : ¬ (C5910.det = 0 ∧ ∀ i, C5910.adjugate i i ≠ 0) := by
  intro h
  have := certificate5910
  rw [h.1] at this
  norm_num at this
def C5911 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5911 : C5911.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5911 : ¬ (C5911.det = 0 ∧ ∀ i, C5911.adjugate i i ≠ 0) := by
  intro h
  have := certificate5911
  rw [h.1] at this
  norm_num at this
def C5912 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5912 : C5912.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5912 : ¬ (C5912.det = 0 ∧ ∀ i, C5912.adjugate i i ≠ 0) := by
  intro h
  have := certificate5912
  rw [h.1] at this
  norm_num at this
def C5913 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5913 : C5913.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5913 : ¬ (C5913.det = 0 ∧ ∀ i, C5913.adjugate i i ≠ 0) := by
  intro h
  have := certificate5913
  rw [h.1] at this
  norm_num at this
def C5914 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5914 : C5914.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5914 : ¬ (C5914.det = 0 ∧ ∀ i, C5914.adjugate i i ≠ 0) := by
  intro h
  have := certificate5914
  rw [h.1] at this
  norm_num at this
def C5915 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5915 : C5915.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5915 : ¬ (C5915.det = 0 ∧ ∀ i, C5915.adjugate i i ≠ 0) := by
  intro h
  have := certificate5915
  rw [h.1] at this
  norm_num at this
def C5916 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5916 : C5916.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5916 : ¬ (C5916.det = 0 ∧ ∀ i, C5916.adjugate i i ≠ 0) := by
  intro h
  have := certificate5916
  rw [h.1] at this
  norm_num at this
def C5917 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5917 : C5917.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5917 : ¬ (C5917.det = 0 ∧ ∀ i, C5917.adjugate i i ≠ 0) := by
  intro h
  have := certificate5917
  rw [h.1] at this
  norm_num at this
def C5918 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5918 : C5918.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5918 : ¬ (C5918.det = 0 ∧ ∀ i, C5918.adjugate i i ≠ 0) := by
  intro h
  have := certificate5918
  rw [h.1] at this
  norm_num at this
def C5919 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5919 : C5919.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5919 : ¬ (C5919.det = 0 ∧ ∀ i, C5919.adjugate i i ≠ 0) := by
  intro h
  have := certificate5919
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0184
