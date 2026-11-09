import VerifiedDet
namespace Nut8.NewCertificates0280
def C8960 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8960 : C8960.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8960 : ¬ (C8960.det = 0 ∧ ∀ i, C8960.adjugate i i ≠ 0) := by
  intro h
  have := certificate8960
  rw [h.1] at this
  norm_num at this
def C8961 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8961 : C8961.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8961 : ¬ (C8961.det = 0 ∧ ∀ i, C8961.adjugate i i ≠ 0) := by
  intro h
  have := certificate8961
  rw [h.1] at this
  norm_num at this
def C8962 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8962 : C8962.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8962 : ¬ (C8962.det = 0 ∧ ∀ i, C8962.adjugate i i ≠ 0) := by
  intro h
  have := certificate8962
  rw [h.1] at this
  norm_num at this
def C8963 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8963 : C8963.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8963 : ¬ (C8963.det = 0 ∧ ∀ i, C8963.adjugate i i ≠ 0) := by
  intro h
  have := certificate8963
  rw [h.1] at this
  norm_num at this
def C8964 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8964 : C8964.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8964 : ¬ (C8964.det = 0 ∧ ∀ i, C8964.adjugate i i ≠ 0) := by
  intro h
  have := certificate8964
  rw [h.1] at this
  norm_num at this
def C8965 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8965 : C8965.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8965 : ¬ (C8965.det = 0 ∧ ∀ i, C8965.adjugate i i ≠ 0) := by
  intro h
  have := certificate8965
  rw [h.1] at this
  norm_num at this
def C8966 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8966 : C8966.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8966 : ¬ (C8966.det = 0 ∧ ∀ i, C8966.adjugate i i ≠ 0) := by
  intro h
  have := certificate8966
  rw [h.1] at this
  norm_num at this
def C8967 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8967 : C8967.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8967 : ¬ (C8967.det = 0 ∧ ∀ i, C8967.adjugate i i ≠ 0) := by
  intro h
  have := certificate8967
  rw [h.1] at this
  norm_num at this
def C8968 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8968 : C8968.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8968 : ¬ (C8968.det = 0 ∧ ∀ i, C8968.adjugate i i ≠ 0) := by
  intro h
  have := certificate8968
  rw [h.1] at this
  norm_num at this
def C8969 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8969 : C8969.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8969 : ¬ (C8969.det = 0 ∧ ∀ i, C8969.adjugate i i ≠ 0) := by
  intro h
  have := certificate8969
  rw [h.1] at this
  norm_num at this
def C8970 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8970 : C8970.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8970 : ¬ (C8970.det = 0 ∧ ∀ i, C8970.adjugate i i ≠ 0) := by
  intro h
  have := certificate8970
  rw [h.1] at this
  norm_num at this
def C8971 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8971 : C8971.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8971 : ¬ (C8971.det = 0 ∧ ∀ i, C8971.adjugate i i ≠ 0) := by
  intro h
  have := certificate8971
  rw [h.1] at this
  norm_num at this
def C8972 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8972 : C8972.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8972 : ¬ (C8972.det = 0 ∧ ∀ i, C8972.adjugate i i ≠ 0) := by
  intro h
  have := certificate8972
  rw [h.1] at this
  norm_num at this
def C8973 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8973 : C8973.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8973 : ¬ (C8973.det = 0 ∧ ∀ i, C8973.adjugate i i ≠ 0) := by
  intro h
  have := certificate8973
  rw [h.1] at this
  norm_num at this
def C8974 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8974 : C8974.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8974 : ¬ (C8974.det = 0 ∧ ∀ i, C8974.adjugate i i ≠ 0) := by
  intro h
  have := certificate8974
  rw [h.1] at this
  norm_num at this
def C8975 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8975 : C8975.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8975 : ¬ (C8975.det = 0 ∧ ∀ i, C8975.adjugate i i ≠ 0) := by
  intro h
  have := certificate8975
  rw [h.1] at this
  norm_num at this
def C8976 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8976 : C8976.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8976 : ¬ (C8976.det = 0 ∧ ∀ i, C8976.adjugate i i ≠ 0) := by
  intro h
  have := certificate8976
  rw [h.1] at this
  norm_num at this
def C8977 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8977 : C8977.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8977 : ¬ (C8977.det = 0 ∧ ∀ i, C8977.adjugate i i ≠ 0) := by
  intro h
  have := certificate8977
  rw [h.1] at this
  norm_num at this
def C8978 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8978 : C8978.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8978 : ¬ (C8978.det = 0 ∧ ∀ i, C8978.adjugate i i ≠ 0) := by
  intro h
  have := certificate8978
  rw [h.1] at this
  norm_num at this
def C8979 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8979 : C8979.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8979 : ¬ (C8979.det = 0 ∧ ∀ i, C8979.adjugate i i ≠ 0) := by
  intro h
  have := certificate8979
  rw [h.1] at this
  norm_num at this
def C8980 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8980 : C8980.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8980 : ¬ (C8980.det = 0 ∧ ∀ i, C8980.adjugate i i ≠ 0) := by
  intro h
  have := certificate8980
  rw [h.1] at this
  norm_num at this
def C8981 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8981 : C8981.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8981 : ¬ (C8981.det = 0 ∧ ∀ i, C8981.adjugate i i ≠ 0) := by
  intro h
  have := certificate8981
  rw [h.1] at this
  norm_num at this
def C8982 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8982 : C8982.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8982 : ¬ (C8982.det = 0 ∧ ∀ i, C8982.adjugate i i ≠ 0) := by
  intro h
  have := certificate8982
  rw [h.1] at this
  norm_num at this
def C8983 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8983 : C8983.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8983 : ¬ (C8983.det = 0 ∧ ∀ i, C8983.adjugate i i ≠ 0) := by
  intro h
  have := certificate8983
  rw [h.1] at this
  norm_num at this
def C8984 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8984 : C8984.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8984 : ¬ (C8984.det = 0 ∧ ∀ i, C8984.adjugate i i ≠ 0) := by
  intro h
  have := certificate8984
  rw [h.1] at this
  norm_num at this
def C8985 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8985 : C8985.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8985 : ¬ (C8985.det = 0 ∧ ∀ i, C8985.adjugate i i ≠ 0) := by
  intro h
  have := certificate8985
  rw [h.1] at this
  norm_num at this
def C8986 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8986 : C8986.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8986 : ¬ (C8986.det = 0 ∧ ∀ i, C8986.adjugate i i ≠ 0) := by
  intro h
  have := certificate8986
  rw [h.1] at this
  norm_num at this
def C8987 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8987 : C8987.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8987 : ¬ (C8987.det = 0 ∧ ∀ i, C8987.adjugate i i ≠ 0) := by
  intro h
  have := certificate8987
  rw [h.1] at this
  norm_num at this
def C8988 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8988 : C8988.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8988 : ¬ (C8988.det = 0 ∧ ∀ i, C8988.adjugate i i ≠ 0) := by
  intro h
  have := certificate8988
  rw [h.1] at this
  norm_num at this
def C8989 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8989 : C8989.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8989 : ¬ (C8989.det = 0 ∧ ∀ i, C8989.adjugate i i ≠ 0) := by
  intro h
  have := certificate8989
  rw [h.1] at this
  norm_num at this
def C8990 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8990 : C8990.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8990 : ¬ (C8990.det = 0 ∧ ∀ i, C8990.adjugate i i ≠ 0) := by
  intro h
  have := certificate8990
  rw [h.1] at this
  norm_num at this
def C8991 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8991 : C8991.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8991 : ¬ (C8991.det = 0 ∧ ∀ i, C8991.adjugate i i ≠ 0) := by
  intro h
  have := certificate8991
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0280
