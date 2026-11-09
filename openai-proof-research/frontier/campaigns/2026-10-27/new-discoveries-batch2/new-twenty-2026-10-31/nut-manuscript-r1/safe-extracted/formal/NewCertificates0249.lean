import VerifiedDet
namespace Nut8.NewCertificates0249
def C7968 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7968 : C7968.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7968 : ¬ (C7968.det = 0 ∧ ∀ i, C7968.adjugate i i ≠ 0) := by
  intro h
  have := certificate7968
  rw [h.1] at this
  norm_num at this
def C7969 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7969 : C7969.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7969 : ¬ (C7969.det = 0 ∧ ∀ i, C7969.adjugate i i ≠ 0) := by
  intro h
  have := certificate7969
  rw [h.1] at this
  norm_num at this
def C7970 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7970 : C7970.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7970 : ¬ (C7970.det = 0 ∧ ∀ i, C7970.adjugate i i ≠ 0) := by
  intro h
  have := certificate7970
  rw [h.1] at this
  norm_num at this
def C7971 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7971 : C7971.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7971 : ¬ (C7971.det = 0 ∧ ∀ i, C7971.adjugate i i ≠ 0) := by
  intro h
  have := certificate7971
  rw [h.1] at this
  norm_num at this
def C7972 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7972 : C7972.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7972 : ¬ (C7972.det = 0 ∧ ∀ i, C7972.adjugate i i ≠ 0) := by
  intro h
  have := certificate7972
  rw [h.1] at this
  norm_num at this
def C7973 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7973 : C7973.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7973 : ¬ (C7973.det = 0 ∧ ∀ i, C7973.adjugate i i ≠ 0) := by
  intro h
  have := certificate7973
  rw [h.1] at this
  norm_num at this
def C7974 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7974 : C7974.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7974 : ¬ (C7974.det = 0 ∧ ∀ i, C7974.adjugate i i ≠ 0) := by
  intro h
  have := certificate7974
  rw [h.1] at this
  norm_num at this
def C7975 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7975 : C7975.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7975 : ¬ (C7975.det = 0 ∧ ∀ i, C7975.adjugate i i ≠ 0) := by
  intro h
  have := certificate7975
  rw [h.1] at this
  norm_num at this
def C7976 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7976 : C7976.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7976 : ¬ (C7976.det = 0 ∧ ∀ i, C7976.adjugate i i ≠ 0) := by
  intro h
  have := certificate7976
  rw [h.1] at this
  norm_num at this
def C7977 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7977 : C7977.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7977 : ¬ (C7977.det = 0 ∧ ∀ i, C7977.adjugate i i ≠ 0) := by
  intro h
  have := certificate7977
  rw [h.1] at this
  norm_num at this
def C7978 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7978 : C7978.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7978 : ¬ (C7978.det = 0 ∧ ∀ i, C7978.adjugate i i ≠ 0) := by
  intro h
  have := certificate7978
  rw [h.1] at this
  norm_num at this
def C7979 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7979 : C7979.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7979 : ¬ (C7979.det = 0 ∧ ∀ i, C7979.adjugate i i ≠ 0) := by
  intro h
  have := certificate7979
  rw [h.1] at this
  norm_num at this
def C7980 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7980 : C7980.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7980 : ¬ (C7980.det = 0 ∧ ∀ i, C7980.adjugate i i ≠ 0) := by
  intro h
  have := certificate7980
  rw [h.1] at this
  norm_num at this
def C7981 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7981 : C7981.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7981 : ¬ (C7981.det = 0 ∧ ∀ i, C7981.adjugate i i ≠ 0) := by
  intro h
  have := certificate7981
  rw [h.1] at this
  norm_num at this
def C7982 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7982 : C7982.det = (93 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7982 : ¬ (C7982.det = 0 ∧ ∀ i, C7982.adjugate i i ≠ 0) := by
  intro h
  have := certificate7982
  rw [h.1] at this
  norm_num at this
def C7983 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7983 : C7983.det = (-43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7983 : ¬ (C7983.det = 0 ∧ ∀ i, C7983.adjugate i i ≠ 0) := by
  intro h
  have := certificate7983
  rw [h.1] at this
  norm_num at this
def C7984 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7984 : C7984.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7984 : ¬ (C7984.det = 0 ∧ ∀ i, C7984.adjugate i i ≠ 0) := by
  intro h
  have := certificate7984
  rw [h.1] at this
  norm_num at this
def C7985 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7985 : C7985.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7985 : ¬ (C7985.det = 0 ∧ ∀ i, C7985.adjugate i i ≠ 0) := by
  intro h
  have := certificate7985
  rw [h.1] at this
  norm_num at this
def C7986 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7986 : C7986.det = (29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7986 : ¬ (C7986.det = 0 ∧ ∀ i, C7986.adjugate i i ≠ 0) := by
  intro h
  have := certificate7986
  rw [h.1] at this
  norm_num at this
def C7987 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7987 : C7987.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7987 : ¬ (C7987.det = 0 ∧ ∀ i, C7987.adjugate i i ≠ 0) := by
  intro h
  have := certificate7987
  rw [h.1] at this
  norm_num at this
def C7988 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7988 : C7988.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7988 : ¬ (C7988.det = 0 ∧ ∀ i, C7988.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7988
def C7989 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7989 : C7989.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7989 : ¬ (C7989.det = 0 ∧ ∀ i, C7989.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7989
def C7990 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7990 : C7990.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7990 : ¬ (C7990.det = 0 ∧ ∀ i, C7990.adjugate i i ≠ 0) := by
  intro h
  have := certificate7990
  rw [h.1] at this
  norm_num at this
def C7991 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7991 : C7991.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7991 : ¬ (C7991.det = 0 ∧ ∀ i, C7991.adjugate i i ≠ 0) := by
  intro h
  have := certificate7991
  rw [h.1] at this
  norm_num at this
def C7992 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7992 : C7992.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7992 : ¬ (C7992.det = 0 ∧ ∀ i, C7992.adjugate i i ≠ 0) := by
  intro h
  have := certificate7992
  rw [h.1] at this
  norm_num at this
def C7993 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7993 : C7993.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7993 : ¬ (C7993.det = 0 ∧ ∀ i, C7993.adjugate i i ≠ 0) := by
  intro h
  have := certificate7993
  rw [h.1] at this
  norm_num at this
def C7994 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7994 : C7994.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7994 : ¬ (C7994.det = 0 ∧ ∀ i, C7994.adjugate i i ≠ 0) := by
  intro h
  have := certificate7994
  rw [h.1] at this
  norm_num at this
def C7995 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7995 : C7995.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7995 : ¬ (C7995.det = 0 ∧ ∀ i, C7995.adjugate i i ≠ 0) := by
  intro h
  have := certificate7995
  rw [h.1] at this
  norm_num at this
def C7996 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7996 : C7996.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7996 : ¬ (C7996.det = 0 ∧ ∀ i, C7996.adjugate i i ≠ 0) := by
  intro h
  have := certificate7996
  rw [h.1] at this
  norm_num at this
def C7997 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7997 : C7997.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7997 : ¬ (C7997.det = 0 ∧ ∀ i, C7997.adjugate i i ≠ 0) := by
  intro h
  have := certificate7997
  rw [h.1] at this
  norm_num at this
def C7998 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7998 : C7998.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7998 : ¬ (C7998.det = 0 ∧ ∀ i, C7998.adjugate i i ≠ 0) := by
  intro h
  have := certificate7998
  rw [h.1] at this
  norm_num at this
def C7999 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7999 : C7999.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7999 : ¬ (C7999.det = 0 ∧ ∀ i, C7999.adjugate i i ≠ 0) := by
  intro h
  have := certificate7999
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0249
