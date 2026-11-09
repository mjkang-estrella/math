import VerifiedDet
namespace Nut8.NewCertificates0031
def C992 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate992 : C992.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction992 : ¬ (C992.det = 0 ∧ ∀ i, C992.adjugate i i ≠ 0) := by
  intro h
  have := certificate992
  rw [h.1] at this
  norm_num at this
def C993 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate993 : C993.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction993 : ¬ (C993.det = 0 ∧ ∀ i, C993.adjugate i i ≠ 0) := by
  intro h
  have := certificate993
  rw [h.1] at this
  norm_num at this
def C994 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate994 : C994.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction994 : ¬ (C994.det = 0 ∧ ∀ i, C994.adjugate i i ≠ 0) := by
  intro h
  have := certificate994
  rw [h.1] at this
  norm_num at this
def C995 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate995 : C995.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction995 : ¬ (C995.det = 0 ∧ ∀ i, C995.adjugate i i ≠ 0) := by
  intro h
  have := certificate995
  rw [h.1] at this
  norm_num at this
def C996 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate996 : C996.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction996 : ¬ (C996.det = 0 ∧ ∀ i, C996.adjugate i i ≠ 0) := by
  intro h
  have := certificate996
  rw [h.1] at this
  norm_num at this
def C997 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate997 : C997.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction997 : ¬ (C997.det = 0 ∧ ∀ i, C997.adjugate i i ≠ 0) := by
  intro h
  have := certificate997
  rw [h.1] at this
  norm_num at this
def C998 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate998 : C998.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction998 : ¬ (C998.det = 0 ∧ ∀ i, C998.adjugate i i ≠ 0) := by
  intro h
  have := certificate998
  rw [h.1] at this
  norm_num at this
def C999 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate999 : C999.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction999 : ¬ (C999.det = 0 ∧ ∀ i, C999.adjugate i i ≠ 0) := by
  intro h
  have := certificate999
  rw [h.1] at this
  norm_num at this
def C1000 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1000 : C1000.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1000 : ¬ (C1000.det = 0 ∧ ∀ i, C1000.adjugate i i ≠ 0) := by
  intro h
  have := certificate1000
  rw [h.1] at this
  norm_num at this
def C1001 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1001 : C1001.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1001 : ¬ (C1001.det = 0 ∧ ∀ i, C1001.adjugate i i ≠ 0) := by
  intro h
  have := certificate1001
  rw [h.1] at this
  norm_num at this
def C1002 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1002 : C1002.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1002 : ¬ (C1002.det = 0 ∧ ∀ i, C1002.adjugate i i ≠ 0) := by
  intro h
  have := certificate1002
  rw [h.1] at this
  norm_num at this
def C1003 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1003 : C1003.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1003 : ¬ (C1003.det = 0 ∧ ∀ i, C1003.adjugate i i ≠ 0) := by
  intro h
  have := certificate1003
  rw [h.1] at this
  norm_num at this
def C1004 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1004 : C1004.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1004 : ¬ (C1004.det = 0 ∧ ∀ i, C1004.adjugate i i ≠ 0) := by
  intro h
  have := certificate1004
  rw [h.1] at this
  norm_num at this
def C1005 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1005 : C1005.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1005 : ¬ (C1005.det = 0 ∧ ∀ i, C1005.adjugate i i ≠ 0) := by
  intro h
  have := certificate1005
  rw [h.1] at this
  norm_num at this
def C1006 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1006 : C1006.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1006 : ¬ (C1006.det = 0 ∧ ∀ i, C1006.adjugate i i ≠ 0) := by
  intro h
  have := certificate1006
  rw [h.1] at this
  norm_num at this
def C1007 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 2, 0, 0]
theorem certificate1007 : C1007.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1007 : ¬ (C1007.det = 0 ∧ ∀ i, C1007.adjugate i i ≠ 0) := by
  intro h
  have := certificate1007
  rw [h.1] at this
  norm_num at this
def C1008 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1008 : C1008.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1008 : ¬ (C1008.det = 0 ∧ ∀ i, C1008.adjugate i i ≠ 0) := by
  intro h
  have := certificate1008
  rw [h.1] at this
  norm_num at this
def C1009 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1009 : C1009.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1009 : ¬ (C1009.det = 0 ∧ ∀ i, C1009.adjugate i i ≠ 0) := by
  intro h
  have := certificate1009
  rw [h.1] at this
  norm_num at this
def C1010 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1010 : C1010.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1010 : ¬ (C1010.det = 0 ∧ ∀ i, C1010.adjugate i i ≠ 0) := by
  intro h
  have := certificate1010
  rw [h.1] at this
  norm_num at this
def C1011 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1011 : C1011.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1011 : ¬ (C1011.det = 0 ∧ ∀ i, C1011.adjugate i i ≠ 0) := by
  intro h
  have := certificate1011
  rw [h.1] at this
  norm_num at this
def C1012 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1012 : C1012.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1012 : ¬ (C1012.det = 0 ∧ ∀ i, C1012.adjugate i i ≠ 0) := by
  intro h
  have := certificate1012
  rw [h.1] at this
  norm_num at this
def C1013 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1013 : C1013.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1013 : ¬ (C1013.det = 0 ∧ ∀ i, C1013.adjugate i i ≠ 0) := by
  intro h
  have := certificate1013
  rw [h.1] at this
  norm_num at this
def C1014 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1014 : C1014.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1014 : ¬ (C1014.det = 0 ∧ ∀ i, C1014.adjugate i i ≠ 0) := by
  intro h
  have := certificate1014
  rw [h.1] at this
  norm_num at this
def C1015 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, -2, 0, 0]
theorem certificate1015 : C1015.det = (-34 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1015 : ¬ (C1015.det = 0 ∧ ∀ i, C1015.adjugate i i ≠ 0) := by
  intro h
  have := certificate1015
  rw [h.1] at this
  norm_num at this
def C1016 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate1016 : C1016.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1016 : ¬ (C1016.det = 0 ∧ ∀ i, C1016.adjugate i i ≠ 0) := by
  intro h
  have := certificate1016
  rw [h.1] at this
  norm_num at this
def C1017 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate1017 : C1017.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1017 : ¬ (C1017.det = 0 ∧ ∀ i, C1017.adjugate i i ≠ 0) := by
  intro h
  have := certificate1017
  rw [h.1] at this
  norm_num at this
def C1018 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate1018 : C1018.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1018 : ¬ (C1018.det = 0 ∧ ∀ i, C1018.adjugate i i ≠ 0) := by
  intro h
  have := certificate1018
  rw [h.1] at this
  norm_num at this
def C1019 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate1019 : C1019.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1019 : ¬ (C1019.det = 0 ∧ ∀ i, C1019.adjugate i i ≠ 0) := by
  intro h
  have := certificate1019
  rw [h.1] at this
  norm_num at this
def C1020 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate1020 : C1020.det = (26 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1020 : ¬ (C1020.det = 0 ∧ ∀ i, C1020.adjugate i i ≠ 0) := by
  intro h
  have := certificate1020
  rw [h.1] at this
  norm_num at this
def C1021 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate1021 : C1021.det = (38 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1021 : ¬ (C1021.det = 0 ∧ ∀ i, C1021.adjugate i i ≠ 0) := by
  intro h
  have := certificate1021
  rw [h.1] at this
  norm_num at this
def C1022 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate1022 : C1022.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1022 : ¬ (C1022.det = 0 ∧ ∀ i, C1022.adjugate i i ≠ 0) := by
  intro h
  have := certificate1022
  rw [h.1] at this
  norm_num at this
def C1023 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate1023 : C1023.det = (-66 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1023 : ¬ (C1023.det = 0 ∧ ∀ i, C1023.adjugate i i ≠ 0) := by
  intro h
  have := certificate1023
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0031
