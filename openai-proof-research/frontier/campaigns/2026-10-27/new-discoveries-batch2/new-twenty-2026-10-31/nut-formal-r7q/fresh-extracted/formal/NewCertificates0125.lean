import VerifiedDet
namespace Nut8.NewCertificates0125
def C4000 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4000 : C4000.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4000 : ¬ (C4000.det = 0 ∧ ∀ i, C4000.adjugate i i ≠ 0) := by
  intro h
  have := certificate4000
  rw [h.1] at this
  norm_num at this
def C4001 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4001 : C4001.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4001 : ¬ (C4001.det = 0 ∧ ∀ i, C4001.adjugate i i ≠ 0) := by
  intro h
  have := certificate4001
  rw [h.1] at this
  norm_num at this
def C4002 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4002 : C4002.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4002 : ¬ (C4002.det = 0 ∧ ∀ i, C4002.adjugate i i ≠ 0) := by
  intro h
  have := certificate4002
  rw [h.1] at this
  norm_num at this
def C4003 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4003 : C4003.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4003 : ¬ (C4003.det = 0 ∧ ∀ i, C4003.adjugate i i ≠ 0) := by
  intro h
  have := certificate4003
  rw [h.1] at this
  norm_num at this
def C4004 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4004 : C4004.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4004 : ¬ (C4004.det = 0 ∧ ∀ i, C4004.adjugate i i ≠ 0) := by
  intro h
  have := certificate4004
  rw [h.1] at this
  norm_num at this
def C4005 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4005 : C4005.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4005 : ¬ (C4005.det = 0 ∧ ∀ i, C4005.adjugate i i ≠ 0) := by
  intro h
  have := certificate4005
  rw [h.1] at this
  norm_num at this
def C4006 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4006 : C4006.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4006 : ¬ (C4006.det = 0 ∧ ∀ i, C4006.adjugate i i ≠ 0) := by
  intro h
  have := certificate4006
  rw [h.1] at this
  norm_num at this
def C4007 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4007 : C4007.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4007 : ¬ (C4007.det = 0 ∧ ∀ i, C4007.adjugate i i ≠ 0) := by
  intro h
  have := certificate4007
  rw [h.1] at this
  norm_num at this
def C4008 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4008 : C4008.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4008 : ¬ (C4008.det = 0 ∧ ∀ i, C4008.adjugate i i ≠ 0) := by
  intro h
  have := certificate4008
  rw [h.1] at this
  norm_num at this
def C4009 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4009 : C4009.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4009 : ¬ (C4009.det = 0 ∧ ∀ i, C4009.adjugate i i ≠ 0) := by
  intro h
  have := certificate4009
  rw [h.1] at this
  norm_num at this
def C4010 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4010 : C4010.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4010 : ¬ (C4010.det = 0 ∧ ∀ i, C4010.adjugate i i ≠ 0) := by
  intro h
  have := certificate4010
  rw [h.1] at this
  norm_num at this
def C4011 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4011 : C4011.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4011 : ¬ (C4011.det = 0 ∧ ∀ i, C4011.adjugate i i ≠ 0) := by
  intro h
  have := certificate4011
  rw [h.1] at this
  norm_num at this
def C4012 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4012 : C4012.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4012 : ¬ (C4012.det = 0 ∧ ∀ i, C4012.adjugate i i ≠ 0) := by
  intro h
  have := certificate4012
  rw [h.1] at this
  norm_num at this
def C4013 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4013 : C4013.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4013 : ¬ (C4013.det = 0 ∧ ∀ i, C4013.adjugate i i ≠ 0) := by
  intro h
  have := certificate4013
  rw [h.1] at this
  norm_num at this
def C4014 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4014 : C4014.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4014 : ¬ (C4014.det = 0 ∧ ∀ i, C4014.adjugate i i ≠ 0) := by
  intro h
  have := certificate4014
  rw [h.1] at this
  norm_num at this
def C4015 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4015 : C4015.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4015 : ¬ (C4015.det = 0 ∧ ∀ i, C4015.adjugate i i ≠ 0) := by
  intro h
  have := certificate4015
  rw [h.1] at this
  norm_num at this
def C4016 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4016 : C4016.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4016 : ¬ (C4016.det = 0 ∧ ∀ i, C4016.adjugate i i ≠ 0) := by
  intro h
  have := certificate4016
  rw [h.1] at this
  norm_num at this
def C4017 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4017 : C4017.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4017 : ¬ (C4017.det = 0 ∧ ∀ i, C4017.adjugate i i ≠ 0) := by
  intro h
  have := certificate4017
  rw [h.1] at this
  norm_num at this
def C4018 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4018 : C4018.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4018 : ¬ (C4018.det = 0 ∧ ∀ i, C4018.adjugate i i ≠ 0) := by
  intro h
  have := certificate4018
  rw [h.1] at this
  norm_num at this
def C4019 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate4019 : C4019.det = (72 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4019 : ¬ (C4019.det = 0 ∧ ∀ i, C4019.adjugate i i ≠ 0) := by
  intro h
  have := certificate4019
  rw [h.1] at this
  norm_num at this
def C4020 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4020 : C4020.det = (52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4020 : ¬ (C4020.det = 0 ∧ ∀ i, C4020.adjugate i i ≠ 0) := by
  intro h
  have := certificate4020
  rw [h.1] at this
  norm_num at this
def C4021 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate4021 : C4021.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4021 : ¬ (C4021.det = 0 ∧ ∀ i, C4021.adjugate i i ≠ 0) := by
  intro h
  have := certificate4021
  rw [h.1] at this
  norm_num at this
def C4022 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4022 : C4022.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4022 : ¬ (C4022.det = 0 ∧ ∀ i, C4022.adjugate i i ≠ 0) := by
  intro h
  have := certificate4022
  rw [h.1] at this
  norm_num at this
def C4023 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4023 : C4023.det = (95 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4023 : ¬ (C4023.det = 0 ∧ ∀ i, C4023.adjugate i i ≠ 0) := by
  intro h
  have := certificate4023
  rw [h.1] at this
  norm_num at this
def C4024 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4024 : C4024.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4024 : ¬ (C4024.det = 0 ∧ ∀ i, C4024.adjugate i i ≠ 0) := by
  intro h
  have := certificate4024
  rw [h.1] at this
  norm_num at this
def C4025 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4025 : C4025.det = (-65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4025 : ¬ (C4025.det = 0 ∧ ∀ i, C4025.adjugate i i ≠ 0) := by
  intro h
  have := certificate4025
  rw [h.1] at this
  norm_num at this
def C4026 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4026 : C4026.det = (-65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4026 : ¬ (C4026.det = 0 ∧ ∀ i, C4026.adjugate i i ≠ 0) := by
  intro h
  have := certificate4026
  rw [h.1] at this
  norm_num at this
def C4027 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4027 : C4027.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4027 : ¬ (C4027.det = 0 ∧ ∀ i, C4027.adjugate i i ≠ 0) := by
  intro h
  have := certificate4027
  rw [h.1] at this
  norm_num at this
def C4028 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate4028 : C4028.det = (95 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4028 : ¬ (C4028.det = 0 ∧ ∀ i, C4028.adjugate i i ≠ 0) := by
  intro h
  have := certificate4028
  rw [h.1] at this
  norm_num at this
def C4029 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate4029 : C4029.det = (63 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4029 : ¬ (C4029.det = 0 ∧ ∀ i, C4029.adjugate i i ≠ 0) := by
  intro h
  have := certificate4029
  rw [h.1] at this
  norm_num at this
def C4030 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4030 : C4030.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4030 : ¬ (C4030.det = 0 ∧ ∀ i, C4030.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4030
def C4031 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4031 : C4031.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4031 : ¬ (C4031.det = 0 ∧ ∀ i, C4031.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4031
end Nut8.NewCertificates0125
