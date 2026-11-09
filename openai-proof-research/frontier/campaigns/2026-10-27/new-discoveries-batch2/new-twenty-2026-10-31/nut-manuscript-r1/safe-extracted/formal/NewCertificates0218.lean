import VerifiedDet
namespace Nut8.NewCertificates0218
def C6976 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6976 : C6976.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6976 : ¬ (C6976.det = 0 ∧ ∀ i, C6976.adjugate i i ≠ 0) := by
  intro h
  have := certificate6976
  rw [h.1] at this
  norm_num at this
def C6977 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6977 : C6977.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6977 : ¬ (C6977.det = 0 ∧ ∀ i, C6977.adjugate i i ≠ 0) := by
  intro h
  have := certificate6977
  rw [h.1] at this
  norm_num at this
def C6978 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6978 : C6978.det = (41 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6978 : ¬ (C6978.det = 0 ∧ ∀ i, C6978.adjugate i i ≠ 0) := by
  intro h
  have := certificate6978
  rw [h.1] at this
  norm_num at this
def C6979 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6979 : C6979.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6979 : ¬ (C6979.det = 0 ∧ ∀ i, C6979.adjugate i i ≠ 0) := by
  intro h
  have := certificate6979
  rw [h.1] at this
  norm_num at this
def C6980 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6980 : C6980.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6980 : ¬ (C6980.det = 0 ∧ ∀ i, C6980.adjugate i i ≠ 0) := by
  intro h
  have := certificate6980
  rw [h.1] at this
  norm_num at this
def C6981 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6981 : C6981.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6981 : ¬ (C6981.det = 0 ∧ ∀ i, C6981.adjugate i i ≠ 0) := by
  intro h
  have := certificate6981
  rw [h.1] at this
  norm_num at this
def C6982 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6982 : C6982.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6982 : ¬ (C6982.det = 0 ∧ ∀ i, C6982.adjugate i i ≠ 0) := by
  intro h
  have := certificate6982
  rw [h.1] at this
  norm_num at this
def C6983 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6983 : C6983.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6983 : ¬ (C6983.det = 0 ∧ ∀ i, C6983.adjugate i i ≠ 0) := by
  intro h
  have := certificate6983
  rw [h.1] at this
  norm_num at this
def C6984 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6984 : C6984.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6984 : ¬ (C6984.det = 0 ∧ ∀ i, C6984.adjugate i i ≠ 0) := by
  intro h
  have := certificate6984
  rw [h.1] at this
  norm_num at this
def C6985 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6985 : C6985.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6985 : ¬ (C6985.det = 0 ∧ ∀ i, C6985.adjugate i i ≠ 0) := by
  intro h
  have := certificate6985
  rw [h.1] at this
  norm_num at this
def C6986 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6986 : C6986.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6986 : ¬ (C6986.det = 0 ∧ ∀ i, C6986.adjugate i i ≠ 0) := by
  intro h
  have := certificate6986
  rw [h.1] at this
  norm_num at this
def C6987 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6987 : C6987.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6987 : ¬ (C6987.det = 0 ∧ ∀ i, C6987.adjugate i i ≠ 0) := by
  intro h
  have := certificate6987
  rw [h.1] at this
  norm_num at this
def C6988 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6988 : C6988.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6988 : ¬ (C6988.det = 0 ∧ ∀ i, C6988.adjugate i i ≠ 0) := by
  intro h
  have := certificate6988
  rw [h.1] at this
  norm_num at this
def C6989 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate6989 : C6989.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6989 : ¬ (C6989.det = 0 ∧ ∀ i, C6989.adjugate i i ≠ 0) := by
  intro h
  have := certificate6989
  rw [h.1] at this
  norm_num at this
def C6990 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6990 : C6990.det = (116 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6990 : ¬ (C6990.det = 0 ∧ ∀ i, C6990.adjugate i i ≠ 0) := by
  intro h
  have := certificate6990
  rw [h.1] at this
  norm_num at this
def C6991 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate6991 : C6991.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6991 : ¬ (C6991.det = 0 ∧ ∀ i, C6991.adjugate i i ≠ 0) := by
  intro h
  have := certificate6991
  rw [h.1] at this
  norm_num at this
def C6992 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6992 : C6992.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6992 : ¬ (C6992.det = 0 ∧ ∀ i, C6992.adjugate i i ≠ 0) := by
  intro h
  have := certificate6992
  rw [h.1] at this
  norm_num at this
def C6993 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6993 : C6993.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6993 : ¬ (C6993.det = 0 ∧ ∀ i, C6993.adjugate i i ≠ 0) := by
  intro h
  have := certificate6993
  rw [h.1] at this
  norm_num at this
def C6994 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6994 : C6994.det = (140 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6994 : ¬ (C6994.det = 0 ∧ ∀ i, C6994.adjugate i i ≠ 0) := by
  intro h
  have := certificate6994
  rw [h.1] at this
  norm_num at this
def C6995 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 2, -1, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6995 : C6995.det = (140 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6995 : ¬ (C6995.det = 0 ∧ ∀ i, C6995.adjugate i i ≠ 0) := by
  intro h
  have := certificate6995
  rw [h.1] at this
  norm_num at this
def C6996 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6996 : C6996.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6996 : ¬ (C6996.det = 0 ∧ ∀ i, C6996.adjugate i i ≠ 0) := by
  intro h
  have := certificate6996
  rw [h.1] at this
  norm_num at this
def C6997 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6997 : C6997.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6997 : ¬ (C6997.det = 0 ∧ ∀ i, C6997.adjugate i i ≠ 0) := by
  intro h
  have := certificate6997
  rw [h.1] at this
  norm_num at this
def C6998 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6998 : C6998.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6998 : ¬ (C6998.det = 0 ∧ ∀ i, C6998.adjugate i i ≠ 0) := by
  intro h
  have := certificate6998
  rw [h.1] at this
  norm_num at this
def C6999 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6999 : C6999.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6999 : ¬ (C6999.det = 0 ∧ ∀ i, C6999.adjugate i i ≠ 0) := by
  intro h
  have := certificate6999
  rw [h.1] at this
  norm_num at this
def C7000 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7000 : C7000.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7000 : ¬ (C7000.det = 0 ∧ ∀ i, C7000.adjugate i i ≠ 0) := by
  intro h
  have := certificate7000
  rw [h.1] at this
  norm_num at this
def C7001 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7001 : C7001.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7001 : ¬ (C7001.det = 0 ∧ ∀ i, C7001.adjugate i i ≠ 0) := by
  intro h
  have := certificate7001
  rw [h.1] at this
  norm_num at this
def C7002 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7002 : C7002.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7002 : ¬ (C7002.det = 0 ∧ ∀ i, C7002.adjugate i i ≠ 0) := by
  intro h
  have := certificate7002
  rw [h.1] at this
  norm_num at this
def C7003 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7003 : C7003.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7003 : ¬ (C7003.det = 0 ∧ ∀ i, C7003.adjugate i i ≠ 0) := by
  intro h
  have := certificate7003
  rw [h.1] at this
  norm_num at this
def C7004 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7004 : C7004.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7004 : ¬ (C7004.det = 0 ∧ ∀ i, C7004.adjugate i i ≠ 0) := by
  intro h
  have := certificate7004
  rw [h.1] at this
  norm_num at this
def C7005 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7005 : C7005.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7005 : ¬ (C7005.det = 0 ∧ ∀ i, C7005.adjugate i i ≠ 0) := by
  intro h
  have := certificate7005
  rw [h.1] at this
  norm_num at this
def C7006 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7006 : C7006.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7006 : ¬ (C7006.det = 0 ∧ ∀ i, C7006.adjugate i i ≠ 0) := by
  intro h
  have := certificate7006
  rw [h.1] at this
  norm_num at this
def C7007 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7007 : C7007.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7007 : ¬ (C7007.det = 0 ∧ ∀ i, C7007.adjugate i i ≠ 0) := by
  intro h
  have := certificate7007
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0218
