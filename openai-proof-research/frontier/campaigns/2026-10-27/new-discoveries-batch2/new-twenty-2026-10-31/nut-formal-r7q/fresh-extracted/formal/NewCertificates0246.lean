import VerifiedDet
namespace Nut8.NewCertificates0246
def C7872 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7872 : C7872.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7872 : ¬ (C7872.det = 0 ∧ ∀ i, C7872.adjugate i i ≠ 0) := by
  intro h
  have := certificate7872
  rw [h.1] at this
  norm_num at this
def C7873 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7873 : C7873.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7873 : ¬ (C7873.det = 0 ∧ ∀ i, C7873.adjugate i i ≠ 0) := by
  intro h
  have := certificate7873
  rw [h.1] at this
  norm_num at this
def C7874 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7874 : C7874.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7874 : ¬ (C7874.det = 0 ∧ ∀ i, C7874.adjugate i i ≠ 0) := by
  intro h
  have := certificate7874
  rw [h.1] at this
  norm_num at this
def C7875 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7875 : C7875.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7875 : ¬ (C7875.det = 0 ∧ ∀ i, C7875.adjugate i i ≠ 0) := by
  intro h
  have := certificate7875
  rw [h.1] at this
  norm_num at this
def C7876 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7876 : C7876.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7876 : ¬ (C7876.det = 0 ∧ ∀ i, C7876.adjugate i i ≠ 0) := by
  intro h
  have := certificate7876
  rw [h.1] at this
  norm_num at this
def C7877 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7877 : C7877.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7877 : ¬ (C7877.det = 0 ∧ ∀ i, C7877.adjugate i i ≠ 0) := by
  intro h
  have := certificate7877
  rw [h.1] at this
  norm_num at this
def C7878 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7878 : C7878.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7878 : ¬ (C7878.det = 0 ∧ ∀ i, C7878.adjugate i i ≠ 0) := by
  intro h
  have := certificate7878
  rw [h.1] at this
  norm_num at this
def C7879 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7879 : C7879.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7879 : ¬ (C7879.det = 0 ∧ ∀ i, C7879.adjugate i i ≠ 0) := by
  intro h
  have := certificate7879
  rw [h.1] at this
  norm_num at this
def C7880 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7880 : C7880.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7880 : ¬ (C7880.det = 0 ∧ ∀ i, C7880.adjugate i i ≠ 0) := by
  intro h
  have := certificate7880
  rw [h.1] at this
  norm_num at this
def C7881 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7881 : C7881.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7881 : ¬ (C7881.det = 0 ∧ ∀ i, C7881.adjugate i i ≠ 0) := by
  intro h
  have := certificate7881
  rw [h.1] at this
  norm_num at this
def C7882 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7882 : C7882.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7882 : ¬ (C7882.det = 0 ∧ ∀ i, C7882.adjugate i i ≠ 0) := by
  intro h
  have := certificate7882
  rw [h.1] at this
  norm_num at this
def C7883 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7883 : C7883.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7883 : ¬ (C7883.det = 0 ∧ ∀ i, C7883.adjugate i i ≠ 0) := by
  intro h
  have := certificate7883
  rw [h.1] at this
  norm_num at this
def C7884 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7884 : C7884.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7884 : ¬ (C7884.det = 0 ∧ ∀ i, C7884.adjugate i i ≠ 0) := by
  intro h
  have := certificate7884
  rw [h.1] at this
  norm_num at this
def C7885 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7885 : C7885.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7885 : ¬ (C7885.det = 0 ∧ ∀ i, C7885.adjugate i i ≠ 0) := by
  intro h
  have := certificate7885
  rw [h.1] at this
  norm_num at this
def C7886 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7886 : C7886.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7886 : ¬ (C7886.det = 0 ∧ ∀ i, C7886.adjugate i i ≠ 0) := by
  intro h
  have := certificate7886
  rw [h.1] at this
  norm_num at this
def C7887 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7887 : C7887.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7887 : ¬ (C7887.det = 0 ∧ ∀ i, C7887.adjugate i i ≠ 0) := by
  intro h
  have := certificate7887
  rw [h.1] at this
  norm_num at this
def C7888 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7888 : C7888.det = (-10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7888 : ¬ (C7888.det = 0 ∧ ∀ i, C7888.adjugate i i ≠ 0) := by
  intro h
  have := certificate7888
  rw [h.1] at this
  norm_num at this
def C7889 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7889 : C7889.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7889 : ¬ (C7889.det = 0 ∧ ∀ i, C7889.adjugate i i ≠ 0) := by
  intro h
  have := certificate7889
  rw [h.1] at this
  norm_num at this
def C7890 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7890 : C7890.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7890 : ¬ (C7890.det = 0 ∧ ∀ i, C7890.adjugate i i ≠ 0) := by
  intro h
  have := certificate7890
  rw [h.1] at this
  norm_num at this
def C7891 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7891 : C7891.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7891 : ¬ (C7891.det = 0 ∧ ∀ i, C7891.adjugate i i ≠ 0) := by
  intro h
  have := certificate7891
  rw [h.1] at this
  norm_num at this
def C7892 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7892 : C7892.det = (-74 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7892 : ¬ (C7892.det = 0 ∧ ∀ i, C7892.adjugate i i ≠ 0) := by
  intro h
  have := certificate7892
  rw [h.1] at this
  norm_num at this
def C7893 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7893 : C7893.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7893 : ¬ (C7893.det = 0 ∧ ∀ i, C7893.adjugate i i ≠ 0) := by
  intro h
  have := certificate7893
  rw [h.1] at this
  norm_num at this
def C7894 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7894 : C7894.det = (70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7894 : ¬ (C7894.det = 0 ∧ ∀ i, C7894.adjugate i i ≠ 0) := by
  intro h
  have := certificate7894
  rw [h.1] at this
  norm_num at this
def C7895 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7895 : C7895.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7895 : ¬ (C7895.det = 0 ∧ ∀ i, C7895.adjugate i i ≠ 0) := by
  intro h
  have := certificate7895
  rw [h.1] at this
  norm_num at this
def C7896 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7896 : C7896.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7896 : ¬ (C7896.det = 0 ∧ ∀ i, C7896.adjugate i i ≠ 0) := by
  intro h
  have := certificate7896
  rw [h.1] at this
  norm_num at this
def C7897 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7897 : C7897.det = (70 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7897 : ¬ (C7897.det = 0 ∧ ∀ i, C7897.adjugate i i ≠ 0) := by
  intro h
  have := certificate7897
  rw [h.1] at this
  norm_num at this
def C7898 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7898 : C7898.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7898 : ¬ (C7898.det = 0 ∧ ∀ i, C7898.adjugate i i ≠ 0) := by
  intro h
  have := certificate7898
  rw [h.1] at this
  norm_num at this
def C7899 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7899 : C7899.det = (-74 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7899 : ¬ (C7899.det = 0 ∧ ∀ i, C7899.adjugate i i ≠ 0) := by
  intro h
  have := certificate7899
  rw [h.1] at this
  norm_num at this
def C7900 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7900 : C7900.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7900 : ¬ (C7900.det = 0 ∧ ∀ i, C7900.adjugate i i ≠ 0) := by
  intro h
  have := certificate7900
  rw [h.1] at this
  norm_num at this
def C7901 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7901 : C7901.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7901 : ¬ (C7901.det = 0 ∧ ∀ i, C7901.adjugate i i ≠ 0) := by
  intro h
  have := certificate7901
  rw [h.1] at this
  norm_num at this
def C7902 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7902 : C7902.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7902 : ¬ (C7902.det = 0 ∧ ∀ i, C7902.adjugate i i ≠ 0) := by
  intro h
  have := certificate7902
  rw [h.1] at this
  norm_num at this
def C7903 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7903 : C7903.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7903 : ¬ (C7903.det = 0 ∧ ∀ i, C7903.adjugate i i ≠ 0) := by
  intro h
  have := certificate7903
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0246
