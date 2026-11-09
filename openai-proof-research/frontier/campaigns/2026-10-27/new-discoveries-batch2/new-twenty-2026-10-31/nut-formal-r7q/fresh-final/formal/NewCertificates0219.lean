import VerifiedDet
namespace Nut8.NewCertificates0219
def C7008 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7008 : C7008.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7008 : ¬ (C7008.det = 0 ∧ ∀ i, C7008.adjugate i i ≠ 0) := by
  intro h
  have := certificate7008
  rw [h.1] at this
  norm_num at this
def C7009 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7009 : C7009.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7009 : ¬ (C7009.det = 0 ∧ ∀ i, C7009.adjugate i i ≠ 0) := by
  intro h
  have := certificate7009
  rw [h.1] at this
  norm_num at this
def C7010 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7010 : C7010.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7010 : ¬ (C7010.det = 0 ∧ ∀ i, C7010.adjugate i i ≠ 0) := by
  intro h
  have := certificate7010
  rw [h.1] at this
  norm_num at this
def C7011 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7011 : C7011.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7011 : ¬ (C7011.det = 0 ∧ ∀ i, C7011.adjugate i i ≠ 0) := by
  intro h
  have := certificate7011
  rw [h.1] at this
  norm_num at this
def C7012 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7012 : C7012.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7012 : ¬ (C7012.det = 0 ∧ ∀ i, C7012.adjugate i i ≠ 0) := by
  intro h
  have := certificate7012
  rw [h.1] at this
  norm_num at this
def C7013 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7013 : C7013.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7013 : ¬ (C7013.det = 0 ∧ ∀ i, C7013.adjugate i i ≠ 0) := by
  intro h
  have := certificate7013
  rw [h.1] at this
  norm_num at this
def C7014 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7014 : C7014.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7014 : ¬ (C7014.det = 0 ∧ ∀ i, C7014.adjugate i i ≠ 0) := by
  intro h
  have := certificate7014
  rw [h.1] at this
  norm_num at this
def C7015 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7015 : C7015.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7015 : ¬ (C7015.det = 0 ∧ ∀ i, C7015.adjugate i i ≠ 0) := by
  intro h
  have := certificate7015
  rw [h.1] at this
  norm_num at this
def C7016 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7016 : C7016.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7016 : ¬ (C7016.det = 0 ∧ ∀ i, C7016.adjugate i i ≠ 0) := by
  intro h
  have := certificate7016
  rw [h.1] at this
  norm_num at this
def C7017 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7017 : C7017.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7017 : ¬ (C7017.det = 0 ∧ ∀ i, C7017.adjugate i i ≠ 0) := by
  intro h
  have := certificate7017
  rw [h.1] at this
  norm_num at this
def C7018 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7018 : C7018.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7018 : ¬ (C7018.det = 0 ∧ ∀ i, C7018.adjugate i i ≠ 0) := by
  intro h
  have := certificate7018
  rw [h.1] at this
  norm_num at this
def C7019 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, -1, 0, 1, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7019 : C7019.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7019 : ¬ (C7019.det = 0 ∧ ∀ i, C7019.adjugate i i ≠ 0) := by
  intro h
  have := certificate7019
  rw [h.1] at this
  norm_num at this
def C7020 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7020 : C7020.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7020 : ¬ (C7020.det = 0 ∧ ∀ i, C7020.adjugate i i ≠ 0) := by
  intro h
  have := certificate7020
  rw [h.1] at this
  norm_num at this
def C7021 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7021 : C7021.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7021 : ¬ (C7021.det = 0 ∧ ∀ i, C7021.adjugate i i ≠ 0) := by
  intro h
  have := certificate7021
  rw [h.1] at this
  norm_num at this
def C7022 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7022 : C7022.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7022 : ¬ (C7022.det = 0 ∧ ∀ i, C7022.adjugate i i ≠ 0) := by
  intro h
  have := certificate7022
  rw [h.1] at this
  norm_num at this
def C7023 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7023 : C7023.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7023 : ¬ (C7023.det = 0 ∧ ∀ i, C7023.adjugate i i ≠ 0) := by
  intro h
  have := certificate7023
  rw [h.1] at this
  norm_num at this
def C7024 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate7024 : C7024.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7024 : ¬ (C7024.det = 0 ∧ ∀ i, C7024.adjugate i i ≠ 0) := by
  intro h
  have := certificate7024
  rw [h.1] at this
  norm_num at this
def C7025 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate7025 : C7025.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7025 : ¬ (C7025.det = 0 ∧ ∀ i, C7025.adjugate i i ≠ 0) := by
  intro h
  have := certificate7025
  rw [h.1] at this
  norm_num at this
def C7026 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate7026 : C7026.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7026 : ¬ (C7026.det = 0 ∧ ∀ i, C7026.adjugate i i ≠ 0) := by
  intro h
  have := certificate7026
  rw [h.1] at this
  norm_num at this
def C7027 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate7027 : C7027.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7027 : ¬ (C7027.det = 0 ∧ ∀ i, C7027.adjugate i i ≠ 0) := by
  intro h
  have := certificate7027
  rw [h.1] at this
  norm_num at this
def C7028 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7028 : C7028.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7028 : ¬ (C7028.det = 0 ∧ ∀ i, C7028.adjugate i i ≠ 0) := by
  intro h
  have := certificate7028
  rw [h.1] at this
  norm_num at this
def C7029 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7029 : C7029.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7029 : ¬ (C7029.det = 0 ∧ ∀ i, C7029.adjugate i i ≠ 0) := by
  intro h
  have := certificate7029
  rw [h.1] at this
  norm_num at this
def C7030 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7030 : C7030.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7030 : ¬ (C7030.det = 0 ∧ ∀ i, C7030.adjugate i i ≠ 0) := by
  intro h
  have := certificate7030
  rw [h.1] at this
  norm_num at this
def C7031 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7031 : C7031.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7031 : ¬ (C7031.det = 0 ∧ ∀ i, C7031.adjugate i i ≠ 0) := by
  intro h
  have := certificate7031
  rw [h.1] at this
  norm_num at this
def C7032 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7032 : C7032.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7032 : ¬ (C7032.det = 0 ∧ ∀ i, C7032.adjugate i i ≠ 0) := by
  intro h
  have := certificate7032
  rw [h.1] at this
  norm_num at this
def C7033 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate7033 : C7033.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7033 : ¬ (C7033.det = 0 ∧ ∀ i, C7033.adjugate i i ≠ 0) := by
  intro h
  have := certificate7033
  rw [h.1] at this
  norm_num at this
def C7034 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7034 : C7034.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7034 : ¬ (C7034.det = 0 ∧ ∀ i, C7034.adjugate i i ≠ 0) := by
  intro h
  have := certificate7034
  rw [h.1] at this
  norm_num at this
def C7035 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 2, -1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate7035 : C7035.det = (65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7035 : ¬ (C7035.det = 0 ∧ ∀ i, C7035.adjugate i i ≠ 0) := by
  intro h
  have := certificate7035
  rw [h.1] at this
  norm_num at this
def C7036 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7036 : C7036.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7036 : ¬ (C7036.det = 0 ∧ ∀ i, C7036.adjugate i i ≠ 0) := by
  intro h
  have := certificate7036
  rw [h.1] at this
  norm_num at this
def C7037 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7037 : C7037.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7037 : ¬ (C7037.det = 0 ∧ ∀ i, C7037.adjugate i i ≠ 0) := by
  intro h
  have := certificate7037
  rw [h.1] at this
  norm_num at this
def C7038 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7038 : C7038.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7038 : ¬ (C7038.det = 0 ∧ ∀ i, C7038.adjugate i i ≠ 0) := by
  intro h
  have := certificate7038
  rw [h.1] at this
  norm_num at this
def C7039 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 2, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7039 : C7039.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7039 : ¬ (C7039.det = 0 ∧ ∀ i, C7039.adjugate i i ≠ 0) := by
  intro h
  have := certificate7039
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0219
