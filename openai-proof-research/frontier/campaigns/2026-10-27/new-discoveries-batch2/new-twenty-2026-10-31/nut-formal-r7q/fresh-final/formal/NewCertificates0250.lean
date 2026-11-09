import VerifiedDet
namespace Nut8.NewCertificates0250
def C8000 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8000 : C8000.det = (91 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8000 : ¬ (C8000.det = 0 ∧ ∀ i, C8000.adjugate i i ≠ 0) := by
  intro h
  have := certificate8000
  rw [h.1] at this
  norm_num at this
def C8001 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate8001 : C8001.det = (91 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8001 : ¬ (C8001.det = 0 ∧ ∀ i, C8001.adjugate i i ≠ 0) := by
  intro h
  have := certificate8001
  rw [h.1] at this
  norm_num at this
def C8002 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8002 : C8002.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8002 : ¬ (C8002.det = 0 ∧ ∀ i, C8002.adjugate i i ≠ 0) := by
  intro h
  have := certificate8002
  rw [h.1] at this
  norm_num at this
def C8003 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate8003 : C8003.det = (35 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8003 : ¬ (C8003.det = 0 ∧ ∀ i, C8003.adjugate i i ≠ 0) := by
  intro h
  have := certificate8003
  rw [h.1] at this
  norm_num at this
def C8004 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8004 : C8004.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8004 : ¬ (C8004.det = 0 ∧ ∀ i, C8004.adjugate i i ≠ 0) := by
  intro h
  have := certificate8004
  rw [h.1] at this
  norm_num at this
def C8005 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8005 : C8005.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8005 : ¬ (C8005.det = 0 ∧ ∀ i, C8005.adjugate i i ≠ 0) := by
  intro h
  have := certificate8005
  rw [h.1] at this
  norm_num at this
def C8006 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8006 : C8006.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8006 : ¬ (C8006.det = 0 ∧ ∀ i, C8006.adjugate i i ≠ 0) := by
  intro h
  have := certificate8006
  rw [h.1] at this
  norm_num at this
def C8007 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8007 : C8007.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8007 : ¬ (C8007.det = 0 ∧ ∀ i, C8007.adjugate i i ≠ 0) := by
  intro h
  have := certificate8007
  rw [h.1] at this
  norm_num at this
def C8008 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8008 : C8008.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8008 : ¬ (C8008.det = 0 ∧ ∀ i, C8008.adjugate i i ≠ 0) := by
  intro h
  have := certificate8008
  rw [h.1] at this
  norm_num at this
def C8009 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8009 : C8009.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8009 : ¬ (C8009.det = 0 ∧ ∀ i, C8009.adjugate i i ≠ 0) := by
  intro h
  have := certificate8009
  rw [h.1] at this
  norm_num at this
def C8010 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8010 : C8010.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8010 : ¬ (C8010.det = 0 ∧ ∀ i, C8010.adjugate i i ≠ 0) := by
  intro h
  have := certificate8010
  rw [h.1] at this
  norm_num at this
def C8011 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8011 : C8011.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8011 : ¬ (C8011.det = 0 ∧ ∀ i, C8011.adjugate i i ≠ 0) := by
  intro h
  have := certificate8011
  rw [h.1] at this
  norm_num at this
def C8012 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8012 : C8012.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8012 : ¬ (C8012.det = 0 ∧ ∀ i, C8012.adjugate i i ≠ 0) := by
  intro h
  have := certificate8012
  rw [h.1] at this
  norm_num at this
def C8013 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8013 : C8013.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8013 : ¬ (C8013.det = 0 ∧ ∀ i, C8013.adjugate i i ≠ 0) := by
  intro h
  have := certificate8013
  rw [h.1] at this
  norm_num at this
def C8014 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8014 : C8014.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8014 : ¬ (C8014.det = 0 ∧ ∀ i, C8014.adjugate i i ≠ 0) := by
  intro h
  have := certificate8014
  rw [h.1] at this
  norm_num at this
def C8015 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8015 : C8015.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8015 : ¬ (C8015.det = 0 ∧ ∀ i, C8015.adjugate i i ≠ 0) := by
  intro h
  have := certificate8015
  rw [h.1] at this
  norm_num at this
def C8016 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8016 : C8016.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8016 : ¬ (C8016.det = 0 ∧ ∀ i, C8016.adjugate i i ≠ 0) := by
  intro h
  have := certificate8016
  rw [h.1] at this
  norm_num at this
def C8017 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8017 : C8017.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8017 : ¬ (C8017.det = 0 ∧ ∀ i, C8017.adjugate i i ≠ 0) := by
  intro h
  have := certificate8017
  rw [h.1] at this
  norm_num at this
def C8018 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8018 : C8018.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8018 : ¬ (C8018.det = 0 ∧ ∀ i, C8018.adjugate i i ≠ 0) := by
  intro h
  have := certificate8018
  rw [h.1] at this
  norm_num at this
def C8019 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8019 : C8019.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8019 : ¬ (C8019.det = 0 ∧ ∀ i, C8019.adjugate i i ≠ 0) := by
  intro h
  have := certificate8019
  rw [h.1] at this
  norm_num at this
def C8020 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8020 : C8020.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8020 : ¬ (C8020.det = 0 ∧ ∀ i, C8020.adjugate i i ≠ 0) := by
  intro h
  have := certificate8020
  rw [h.1] at this
  norm_num at this
def C8021 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8021 : C8021.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8021 : ¬ (C8021.det = 0 ∧ ∀ i, C8021.adjugate i i ≠ 0) := by
  intro h
  have := certificate8021
  rw [h.1] at this
  norm_num at this
def C8022 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8022 : C8022.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8022 : ¬ (C8022.det = 0 ∧ ∀ i, C8022.adjugate i i ≠ 0) := by
  intro h
  have := certificate8022
  rw [h.1] at this
  norm_num at this
def C8023 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8023 : C8023.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8023 : ¬ (C8023.det = 0 ∧ ∀ i, C8023.adjugate i i ≠ 0) := by
  intro h
  have := certificate8023
  rw [h.1] at this
  norm_num at this
def C8024 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8024 : C8024.det = (-30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8024 : ¬ (C8024.det = 0 ∧ ∀ i, C8024.adjugate i i ≠ 0) := by
  intro h
  have := certificate8024
  rw [h.1] at this
  norm_num at this
def C8025 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8025 : C8025.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8025 : ¬ (C8025.det = 0 ∧ ∀ i, C8025.adjugate i i ≠ 0) := by
  intro h
  have := certificate8025
  rw [h.1] at this
  norm_num at this
def C8026 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8026 : C8026.det = (78 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8026 : ¬ (C8026.det = 0 ∧ ∀ i, C8026.adjugate i i ≠ 0) := by
  intro h
  have := certificate8026
  rw [h.1] at this
  norm_num at this
def C8027 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8027 : C8027.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8027 : ¬ (C8027.det = 0 ∧ ∀ i, C8027.adjugate i i ≠ 0) := by
  intro h
  have := certificate8027
  rw [h.1] at this
  norm_num at this
def C8028 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8028 : C8028.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8028 : ¬ (C8028.det = 0 ∧ ∀ i, C8028.adjugate i i ≠ 0) := by
  intro h
  have := certificate8028
  rw [h.1] at this
  norm_num at this
def C8029 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8029 : C8029.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8029 : ¬ (C8029.det = 0 ∧ ∀ i, C8029.adjugate i i ≠ 0) := by
  intro h
  have := certificate8029
  rw [h.1] at this
  norm_num at this
def C8030 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8030 : C8030.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8030 : ¬ (C8030.det = 0 ∧ ∀ i, C8030.adjugate i i ≠ 0) := by
  intro h
  have := certificate8030
  rw [h.1] at this
  norm_num at this
def C8031 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8031 : C8031.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8031 : ¬ (C8031.det = 0 ∧ ∀ i, C8031.adjugate i i ≠ 0) := by
  intro h
  have := certificate8031
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0250
