import VerifiedDet
namespace Nut8.NewCertificates0062
def C1984 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1984 : C1984.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1984 : ¬ (C1984.det = 0 ∧ ∀ i, C1984.adjugate i i ≠ 0) := by
  intro h
  have := certificate1984
  rw [h.1] at this
  norm_num at this
def C1985 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1985 : C1985.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1985 : ¬ (C1985.det = 0 ∧ ∀ i, C1985.adjugate i i ≠ 0) := by
  intro h
  have := certificate1985
  rw [h.1] at this
  norm_num at this
def C1986 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1986 : C1986.det = (-19 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1986 : ¬ (C1986.det = 0 ∧ ∀ i, C1986.adjugate i i ≠ 0) := by
  intro h
  have := certificate1986
  rw [h.1] at this
  norm_num at this
def C1987 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1987 : C1987.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1987 : ¬ (C1987.det = 0 ∧ ∀ i, C1987.adjugate i i ≠ 0) := by
  intro h
  have := certificate1987
  rw [h.1] at this
  norm_num at this
def C1988 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1988 : C1988.det = (37 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1988 : ¬ (C1988.det = 0 ∧ ∀ i, C1988.adjugate i i ≠ 0) := by
  intro h
  have := certificate1988
  rw [h.1] at this
  norm_num at this
def C1989 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1989 : C1989.det = (-51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1989 : ¬ (C1989.det = 0 ∧ ∀ i, C1989.adjugate i i ≠ 0) := by
  intro h
  have := certificate1989
  rw [h.1] at this
  norm_num at this
def C1990 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1990 : C1990.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1990 : ¬ (C1990.det = 0 ∧ ∀ i, C1990.adjugate i i ≠ 0) := by
  intro h
  have := certificate1990
  rw [h.1] at this
  norm_num at this
def C1991 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1991 : C1991.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1991 : ¬ (C1991.det = 0 ∧ ∀ i, C1991.adjugate i i ≠ 0) := by
  intro h
  have := certificate1991
  rw [h.1] at this
  norm_num at this
def C1992 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1992 : C1992.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1992 : ¬ (C1992.det = 0 ∧ ∀ i, C1992.adjugate i i ≠ 0) := by
  intro h
  have := certificate1992
  rw [h.1] at this
  norm_num at this
def C1993 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1993 : C1993.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1993 : ¬ (C1993.det = 0 ∧ ∀ i, C1993.adjugate i i ≠ 0) := by
  intro h
  have := certificate1993
  rw [h.1] at this
  norm_num at this
def C1994 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1994 : C1994.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1994 : ¬ (C1994.det = 0 ∧ ∀ i, C1994.adjugate i i ≠ 0) := by
  intro h
  have := certificate1994
  rw [h.1] at this
  norm_num at this
def C1995 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1995 : C1995.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1995 : ¬ (C1995.det = 0 ∧ ∀ i, C1995.adjugate i i ≠ 0) := by
  intro h
  have := certificate1995
  rw [h.1] at this
  norm_num at this
def C1996 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1996 : C1996.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1996 : ¬ (C1996.det = 0 ∧ ∀ i, C1996.adjugate i i ≠ 0) := by
  intro h
  have := certificate1996
  rw [h.1] at this
  norm_num at this
def C1997 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate1997 : C1997.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1997 : ¬ (C1997.det = 0 ∧ ∀ i, C1997.adjugate i i ≠ 0) := by
  intro h
  have := certificate1997
  rw [h.1] at this
  norm_num at this
def C1998 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1998 : C1998.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1998 : ¬ (C1998.det = 0 ∧ ∀ i, C1998.adjugate i i ≠ 0) := by
  intro h
  have := certificate1998
  rw [h.1] at this
  norm_num at this
def C1999 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate1999 : C1999.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction1999 : ¬ (C1999.det = 0 ∧ ∀ i, C1999.adjugate i i ≠ 0) := by
  intro h
  have := certificate1999
  rw [h.1] at this
  norm_num at this
def C2000 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2000 : C2000.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2000 : ¬ (C2000.det = 0 ∧ ∀ i, C2000.adjugate i i ≠ 0) := by
  intro h
  have := certificate2000
  rw [h.1] at this
  norm_num at this
def C2001 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2001 : C2001.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2001 : ¬ (C2001.det = 0 ∧ ∀ i, C2001.adjugate i i ≠ 0) := by
  intro h
  have := certificate2001
  rw [h.1] at this
  norm_num at this
def C2002 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2002 : C2002.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2002 : ¬ (C2002.det = 0 ∧ ∀ i, C2002.adjugate i i ≠ 0) := by
  intro h
  have := certificate2002
  rw [h.1] at this
  norm_num at this
def C2003 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2003 : C2003.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2003 : ¬ (C2003.det = 0 ∧ ∀ i, C2003.adjugate i i ≠ 0) := by
  intro h
  have := certificate2003
  rw [h.1] at this
  norm_num at this
def C2004 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2004 : C2004.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2004 : ¬ (C2004.det = 0 ∧ ∀ i, C2004.adjugate i i ≠ 0) := by
  intro h
  have := certificate2004
  rw [h.1] at this
  norm_num at this
def C2005 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2005 : C2005.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2005 : ¬ (C2005.det = 0 ∧ ∀ i, C2005.adjugate i i ≠ 0) := by
  intro h
  have := certificate2005
  rw [h.1] at this
  norm_num at this
def C2006 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2006 : C2006.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2006 : ¬ (C2006.det = 0 ∧ ∀ i, C2006.adjugate i i ≠ 0) := by
  intro h
  have := certificate2006
  rw [h.1] at this
  norm_num at this
def C2007 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2007 : C2007.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2007 : ¬ (C2007.det = 0 ∧ ∀ i, C2007.adjugate i i ≠ 0) := by
  intro h
  have := certificate2007
  rw [h.1] at this
  norm_num at this
def C2008 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2008 : C2008.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2008 : ¬ (C2008.det = 0 ∧ ∀ i, C2008.adjugate i i ≠ 0) := by
  intro h
  have := certificate2008
  rw [h.1] at this
  norm_num at this
def C2009 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2009 : C2009.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2009 : ¬ (C2009.det = 0 ∧ ∀ i, C2009.adjugate i i ≠ 0) := by
  intro h
  have := certificate2009
  rw [h.1] at this
  norm_num at this
def C2010 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2010 : C2010.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2010 : ¬ (C2010.det = 0 ∧ ∀ i, C2010.adjugate i i ≠ 0) := by
  intro h
  have := certificate2010
  rw [h.1] at this
  norm_num at this
def C2011 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2011 : C2011.det = (-42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2011 : ¬ (C2011.det = 0 ∧ ∀ i, C2011.adjugate i i ≠ 0) := by
  intro h
  have := certificate2011
  rw [h.1] at this
  norm_num at this
def C2012 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2012 : C2012.det = (-50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2012 : ¬ (C2012.det = 0 ∧ ∀ i, C2012.adjugate i i ≠ 0) := by
  intro h
  have := certificate2012
  rw [h.1] at this
  norm_num at this
def C2013 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate2013 : C2013.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2013 : ¬ (C2013.det = 0 ∧ ∀ i, C2013.adjugate i i ≠ 0) := by
  intro h
  have := certificate2013
  rw [h.1] at this
  norm_num at this
def C2014 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2014 : C2014.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2014 : ¬ (C2014.det = 0 ∧ ∀ i, C2014.adjugate i i ≠ 0) := by
  intro h
  have := certificate2014
  rw [h.1] at this
  norm_num at this
def C2015 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate2015 : C2015.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2015 : ¬ (C2015.det = 0 ∧ ∀ i, C2015.adjugate i i ≠ 0) := by
  intro h
  have := certificate2015
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0062
