import VerifiedDet
namespace Nut8.NewCertificates0281
def C8992 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8992 : C8992.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8992 : ¬ (C8992.det = 0 ∧ ∀ i, C8992.adjugate i i ≠ 0) := by
  intro h
  have := certificate8992
  rw [h.1] at this
  norm_num at this
def C8993 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate8993 : C8993.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8993 : ¬ (C8993.det = 0 ∧ ∀ i, C8993.adjugate i i ≠ 0) := by
  intro h
  have := certificate8993
  rw [h.1] at this
  norm_num at this
def C8994 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8994 : C8994.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8994 : ¬ (C8994.det = 0 ∧ ∀ i, C8994.adjugate i i ≠ 0) := by
  intro h
  have := certificate8994
  rw [h.1] at this
  norm_num at this
def C8995 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate8995 : C8995.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8995 : ¬ (C8995.det = 0 ∧ ∀ i, C8995.adjugate i i ≠ 0) := by
  intro h
  have := certificate8995
  rw [h.1] at this
  norm_num at this
def C8996 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8996 : C8996.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8996 : ¬ (C8996.det = 0 ∧ ∀ i, C8996.adjugate i i ≠ 0) := by
  intro h
  have := certificate8996
  rw [h.1] at this
  norm_num at this
def C8997 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate8997 : C8997.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8997 : ¬ (C8997.det = 0 ∧ ∀ i, C8997.adjugate i i ≠ 0) := by
  intro h
  have := certificate8997
  rw [h.1] at this
  norm_num at this
def C8998 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8998 : C8998.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8998 : ¬ (C8998.det = 0 ∧ ∀ i, C8998.adjugate i i ≠ 0) := by
  intro h
  have := certificate8998
  rw [h.1] at this
  norm_num at this
def C8999 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate8999 : C8999.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8999 : ¬ (C8999.det = 0 ∧ ∀ i, C8999.adjugate i i ≠ 0) := by
  intro h
  have := certificate8999
  rw [h.1] at this
  norm_num at this
def C9000 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9000 : C9000.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9000 : ¬ (C9000.det = 0 ∧ ∀ i, C9000.adjugate i i ≠ 0) := by
  intro h
  have := certificate9000
  rw [h.1] at this
  norm_num at this
def C9001 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9001 : C9001.det = (19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9001 : ¬ (C9001.det = 0 ∧ ∀ i, C9001.adjugate i i ≠ 0) := by
  intro h
  have := certificate9001
  rw [h.1] at this
  norm_num at this
def C9002 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9002 : C9002.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9002 : ¬ (C9002.det = 0 ∧ ∀ i, C9002.adjugate i i ≠ 0) := by
  intro h
  have := certificate9002
  rw [h.1] at this
  norm_num at this
def C9003 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9003 : C9003.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9003 : ¬ (C9003.det = 0 ∧ ∀ i, C9003.adjugate i i ≠ 0) := by
  intro h
  have := certificate9003
  rw [h.1] at this
  norm_num at this
def C9004 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9004 : C9004.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9004 : ¬ (C9004.det = 0 ∧ ∀ i, C9004.adjugate i i ≠ 0) := by
  intro h
  have := certificate9004
  rw [h.1] at this
  norm_num at this
def C9005 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9005 : C9005.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9005 : ¬ (C9005.det = 0 ∧ ∀ i, C9005.adjugate i i ≠ 0) := by
  intro h
  have := certificate9005
  rw [h.1] at this
  norm_num at this
def C9006 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9006 : C9006.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9006 : ¬ (C9006.det = 0 ∧ ∀ i, C9006.adjugate i i ≠ 0) := by
  intro h
  have := certificate9006
  rw [h.1] at this
  norm_num at this
def C9007 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9007 : C9007.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9007 : ¬ (C9007.det = 0 ∧ ∀ i, C9007.adjugate i i ≠ 0) := by
  intro h
  have := certificate9007
  rw [h.1] at this
  norm_num at this
def C9008 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9008 : C9008.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9008 : ¬ (C9008.det = 0 ∧ ∀ i, C9008.adjugate i i ≠ 0) := by
  intro h
  have := certificate9008
  rw [h.1] at this
  norm_num at this
def C9009 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9009 : C9009.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9009 : ¬ (C9009.det = 0 ∧ ∀ i, C9009.adjugate i i ≠ 0) := by
  intro h
  have := certificate9009
  rw [h.1] at this
  norm_num at this
def C9010 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9010 : C9010.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9010 : ¬ (C9010.det = 0 ∧ ∀ i, C9010.adjugate i i ≠ 0) := by
  intro h
  have := certificate9010
  rw [h.1] at this
  norm_num at this
def C9011 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9011 : C9011.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9011 : ¬ (C9011.det = 0 ∧ ∀ i, C9011.adjugate i i ≠ 0) := by
  intro h
  have := certificate9011
  rw [h.1] at this
  norm_num at this
def C9012 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9012 : C9012.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9012 : ¬ (C9012.det = 0 ∧ ∀ i, C9012.adjugate i i ≠ 0) := by
  intro h
  have := certificate9012
  rw [h.1] at this
  norm_num at this
def C9013 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9013 : C9013.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9013 : ¬ (C9013.det = 0 ∧ ∀ i, C9013.adjugate i i ≠ 0) := by
  intro h
  have := certificate9013
  rw [h.1] at this
  norm_num at this
def C9014 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9014 : C9014.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9014 : ¬ (C9014.det = 0 ∧ ∀ i, C9014.adjugate i i ≠ 0) := by
  intro h
  have := certificate9014
  rw [h.1] at this
  norm_num at this
def C9015 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9015 : C9015.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9015 : ¬ (C9015.det = 0 ∧ ∀ i, C9015.adjugate i i ≠ 0) := by
  intro h
  have := certificate9015
  rw [h.1] at this
  norm_num at this
def C9016 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9016 : C9016.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9016 : ¬ (C9016.det = 0 ∧ ∀ i, C9016.adjugate i i ≠ 0) := by
  intro h
  have := certificate9016
  rw [h.1] at this
  norm_num at this
def C9017 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9017 : C9017.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9017 : ¬ (C9017.det = 0 ∧ ∀ i, C9017.adjugate i i ≠ 0) := by
  intro h
  have := certificate9017
  rw [h.1] at this
  norm_num at this
def C9018 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9018 : C9018.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9018 : ¬ (C9018.det = 0 ∧ ∀ i, C9018.adjugate i i ≠ 0) := by
  intro h
  have := certificate9018
  rw [h.1] at this
  norm_num at this
def C9019 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9019 : C9019.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9019 : ¬ (C9019.det = 0 ∧ ∀ i, C9019.adjugate i i ≠ 0) := by
  intro h
  have := certificate9019
  rw [h.1] at this
  norm_num at this
def C9020 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate9020 : C9020.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9020 : ¬ (C9020.det = 0 ∧ ∀ i, C9020.adjugate i i ≠ 0) := by
  intro h
  have := certificate9020
  rw [h.1] at this
  norm_num at this
def C9021 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate9021 : C9021.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9021 : ¬ (C9021.det = 0 ∧ ∀ i, C9021.adjugate i i ≠ 0) := by
  intro h
  have := certificate9021
  rw [h.1] at this
  norm_num at this
def C9022 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate9022 : C9022.det = (57 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9022 : ¬ (C9022.det = 0 ∧ ∀ i, C9022.adjugate i i ≠ 0) := by
  intro h
  have := certificate9022
  rw [h.1] at this
  norm_num at this
def C9023 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate9023 : C9023.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction9023 : ¬ (C9023.det = 0 ∧ ∀ i, C9023.adjugate i i ≠ 0) := by
  intro h
  have := certificate9023
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0281
