import VerifiedDet
namespace Nut8.NewCertificates0187
def C5984 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5984 : C5984.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5984 : ¬ (C5984.det = 0 ∧ ∀ i, C5984.adjugate i i ≠ 0) := by
  intro h
  have := certificate5984
  rw [h.1] at this
  norm_num at this
def C5985 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5985 : C5985.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5985 : ¬ (C5985.det = 0 ∧ ∀ i, C5985.adjugate i i ≠ 0) := by
  intro h
  have := certificate5985
  rw [h.1] at this
  norm_num at this
def C5986 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5986 : C5986.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5986 : ¬ (C5986.det = 0 ∧ ∀ i, C5986.adjugate i i ≠ 0) := by
  intro h
  have := certificate5986
  rw [h.1] at this
  norm_num at this
def C5987 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5987 : C5987.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5987 : ¬ (C5987.det = 0 ∧ ∀ i, C5987.adjugate i i ≠ 0) := by
  intro h
  have := certificate5987
  rw [h.1] at this
  norm_num at this
def C5988 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5988 : C5988.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5988 : ¬ (C5988.det = 0 ∧ ∀ i, C5988.adjugate i i ≠ 0) := by
  intro h
  have := certificate5988
  rw [h.1] at this
  norm_num at this
def C5989 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5989 : C5989.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5989 : ¬ (C5989.det = 0 ∧ ∀ i, C5989.adjugate i i ≠ 0) := by
  intro h
  have := certificate5989
  rw [h.1] at this
  norm_num at this
def C5990 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5990 : C5990.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5990 : ¬ (C5990.det = 0 ∧ ∀ i, C5990.adjugate i i ≠ 0) := by
  intro h
  have := certificate5990
  rw [h.1] at this
  norm_num at this
def C5991 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5991 : C5991.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5991 : ¬ (C5991.det = 0 ∧ ∀ i, C5991.adjugate i i ≠ 0) := by
  intro h
  have := certificate5991
  rw [h.1] at this
  norm_num at this
def C5992 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5992 : C5992.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5992 : ¬ (C5992.det = 0 ∧ ∀ i, C5992.adjugate i i ≠ 0) := by
  intro h
  have := certificate5992
  rw [h.1] at this
  norm_num at this
def C5993 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5993 : C5993.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5993 : ¬ (C5993.det = 0 ∧ ∀ i, C5993.adjugate i i ≠ 0) := by
  intro h
  have := certificate5993
  rw [h.1] at this
  norm_num at this
def C5994 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5994 : C5994.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5994 : ¬ (C5994.det = 0 ∧ ∀ i, C5994.adjugate i i ≠ 0) := by
  intro h
  have := certificate5994
  rw [h.1] at this
  norm_num at this
def C5995 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5995 : C5995.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5995 : ¬ (C5995.det = 0 ∧ ∀ i, C5995.adjugate i i ≠ 0) := by
  intro h
  have := certificate5995
  rw [h.1] at this
  norm_num at this
def C5996 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5996 : C5996.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5996 : ¬ (C5996.det = 0 ∧ ∀ i, C5996.adjugate i i ≠ 0) := by
  intro h
  have := certificate5996
  rw [h.1] at this
  norm_num at this
def C5997 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5997 : C5997.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5997 : ¬ (C5997.det = 0 ∧ ∀ i, C5997.adjugate i i ≠ 0) := by
  intro h
  have := certificate5997
  rw [h.1] at this
  norm_num at this
def C5998 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5998 : C5998.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5998 : ¬ (C5998.det = 0 ∧ ∀ i, C5998.adjugate i i ≠ 0) := by
  intro h
  have := certificate5998
  rw [h.1] at this
  norm_num at this
def C5999 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5999 : C5999.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5999 : ¬ (C5999.det = 0 ∧ ∀ i, C5999.adjugate i i ≠ 0) := by
  intro h
  have := certificate5999
  rw [h.1] at this
  norm_num at this
def C6000 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6000 : C6000.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6000 : ¬ (C6000.det = 0 ∧ ∀ i, C6000.adjugate i i ≠ 0) := by
  intro h
  have := certificate6000
  rw [h.1] at this
  norm_num at this
def C6001 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6001 : C6001.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6001 : ¬ (C6001.det = 0 ∧ ∀ i, C6001.adjugate i i ≠ 0) := by
  intro h
  have := certificate6001
  rw [h.1] at this
  norm_num at this
def C6002 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6002 : C6002.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6002 : ¬ (C6002.det = 0 ∧ ∀ i, C6002.adjugate i i ≠ 0) := by
  intro h
  have := certificate6002
  rw [h.1] at this
  norm_num at this
def C6003 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6003 : C6003.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6003 : ¬ (C6003.det = 0 ∧ ∀ i, C6003.adjugate i i ≠ 0) := by
  intro h
  have := certificate6003
  rw [h.1] at this
  norm_num at this
def C6004 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6004 : C6004.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6004 : ¬ (C6004.det = 0 ∧ ∀ i, C6004.adjugate i i ≠ 0) := by
  intro h
  have := certificate6004
  rw [h.1] at this
  norm_num at this
def C6005 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6005 : C6005.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6005 : ¬ (C6005.det = 0 ∧ ∀ i, C6005.adjugate i i ≠ 0) := by
  intro h
  have := certificate6005
  rw [h.1] at this
  norm_num at this
def C6006 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6006 : C6006.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6006 : ¬ (C6006.det = 0 ∧ ∀ i, C6006.adjugate i i ≠ 0) := by
  intro h
  have := certificate6006
  rw [h.1] at this
  norm_num at this
def C6007 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6007 : C6007.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6007 : ¬ (C6007.det = 0 ∧ ∀ i, C6007.adjugate i i ≠ 0) := by
  intro h
  have := certificate6007
  rw [h.1] at this
  norm_num at this
def C6008 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6008 : C6008.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6008 : ¬ (C6008.det = 0 ∧ ∀ i, C6008.adjugate i i ≠ 0) := by
  intro h
  have := certificate6008
  rw [h.1] at this
  norm_num at this
def C6009 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate6009 : C6009.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6009 : ¬ (C6009.det = 0 ∧ ∀ i, C6009.adjugate i i ≠ 0) := by
  intro h
  have := certificate6009
  rw [h.1] at this
  norm_num at this
def C6010 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6010 : C6010.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6010 : ¬ (C6010.det = 0 ∧ ∀ i, C6010.adjugate i i ≠ 0) := by
  intro h
  have := certificate6010
  rw [h.1] at this
  norm_num at this
def C6011 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate6011 : C6011.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6011 : ¬ (C6011.det = 0 ∧ ∀ i, C6011.adjugate i i ≠ 0) := by
  intro h
  have := certificate6011
  rw [h.1] at this
  norm_num at this
def C6012 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6012 : C6012.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6012 : ¬ (C6012.det = 0 ∧ ∀ i, C6012.adjugate i i ≠ 0) := by
  intro h
  have := certificate6012
  rw [h.1] at this
  norm_num at this
def C6013 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6013 : C6013.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6013 : ¬ (C6013.det = 0 ∧ ∀ i, C6013.adjugate i i ≠ 0) := by
  intro h
  have := certificate6013
  rw [h.1] at this
  norm_num at this
def C6014 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6014 : C6014.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6014 : ¬ (C6014.det = 0 ∧ ∀ i, C6014.adjugate i i ≠ 0) := by
  intro h
  have := certificate6014
  rw [h.1] at this
  norm_num at this
def C6015 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6015 : C6015.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6015 : ¬ (C6015.det = 0 ∧ ∀ i, C6015.adjugate i i ≠ 0) := by
  intro h
  have := certificate6015
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0187
