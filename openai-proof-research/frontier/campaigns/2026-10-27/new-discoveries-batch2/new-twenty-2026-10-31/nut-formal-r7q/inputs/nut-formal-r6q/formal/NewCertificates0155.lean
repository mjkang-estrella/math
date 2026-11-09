import VerifiedDet
namespace Nut8.NewCertificates0155
def C4960 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4960 : C4960.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4960 : ¬ (C4960.det = 0 ∧ ∀ i, C4960.adjugate i i ≠ 0) := by
  intro h
  have := certificate4960
  rw [h.1] at this
  norm_num at this
def C4961 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4961 : C4961.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4961 : ¬ (C4961.det = 0 ∧ ∀ i, C4961.adjugate i i ≠ 0) := by
  intro h
  have := certificate4961
  rw [h.1] at this
  norm_num at this
def C4962 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4962 : C4962.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4962 : ¬ (C4962.det = 0 ∧ ∀ i, C4962.adjugate i i ≠ 0) := by
  intro h
  have := certificate4962
  rw [h.1] at this
  norm_num at this
def C4963 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4963 : C4963.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4963 : ¬ (C4963.det = 0 ∧ ∀ i, C4963.adjugate i i ≠ 0) := by
  intro h
  have := certificate4963
  rw [h.1] at this
  norm_num at this
def C4964 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4964 : C4964.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4964 : ¬ (C4964.det = 0 ∧ ∀ i, C4964.adjugate i i ≠ 0) := by
  intro h
  have := certificate4964
  rw [h.1] at this
  norm_num at this
def C4965 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4965 : C4965.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4965 : ¬ (C4965.det = 0 ∧ ∀ i, C4965.adjugate i i ≠ 0) := by
  intro h
  have := certificate4965
  rw [h.1] at this
  norm_num at this
def C4966 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4966 : C4966.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4966 : ¬ (C4966.det = 0 ∧ ∀ i, C4966.adjugate i i ≠ 0) := by
  intro h
  have := certificate4966
  rw [h.1] at this
  norm_num at this
def C4967 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4967 : C4967.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4967 : ¬ (C4967.det = 0 ∧ ∀ i, C4967.adjugate i i ≠ 0) := by
  intro h
  have := certificate4967
  rw [h.1] at this
  norm_num at this
def C4968 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4968 : C4968.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4968 : ¬ (C4968.det = 0 ∧ ∀ i, C4968.adjugate i i ≠ 0) := by
  intro h
  have := certificate4968
  rw [h.1] at this
  norm_num at this
def C4969 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4969 : C4969.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4969 : ¬ (C4969.det = 0 ∧ ∀ i, C4969.adjugate i i ≠ 0) := by
  intro h
  have := certificate4969
  rw [h.1] at this
  norm_num at this
def C4970 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4970 : C4970.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4970 : ¬ (C4970.det = 0 ∧ ∀ i, C4970.adjugate i i ≠ 0) := by
  intro h
  have := certificate4970
  rw [h.1] at this
  norm_num at this
def C4971 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4971 : C4971.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4971 : ¬ (C4971.det = 0 ∧ ∀ i, C4971.adjugate i i ≠ 0) := by
  intro h
  have := certificate4971
  rw [h.1] at this
  norm_num at this
def C4972 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4972 : C4972.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4972 : ¬ (C4972.det = 0 ∧ ∀ i, C4972.adjugate i i ≠ 0) := by
  intro h
  have := certificate4972
  rw [h.1] at this
  norm_num at this
def C4973 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4973 : C4973.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4973 : ¬ (C4973.det = 0 ∧ ∀ i, C4973.adjugate i i ≠ 0) := by
  intro h
  have := certificate4973
  rw [h.1] at this
  norm_num at this
def C4974 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4974 : C4974.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4974 : ¬ (C4974.det = 0 ∧ ∀ i, C4974.adjugate i i ≠ 0) := by
  intro h
  have := certificate4974
  rw [h.1] at this
  norm_num at this
def C4975 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4975 : C4975.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4975 : ¬ (C4975.det = 0 ∧ ∀ i, C4975.adjugate i i ≠ 0) := by
  intro h
  have := certificate4975
  rw [h.1] at this
  norm_num at this
def C4976 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4976 : C4976.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4976 : ¬ (C4976.det = 0 ∧ ∀ i, C4976.adjugate i i ≠ 0) := by
  intro h
  have := certificate4976
  rw [h.1] at this
  norm_num at this
def C4977 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4977 : C4977.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4977 : ¬ (C4977.det = 0 ∧ ∀ i, C4977.adjugate i i ≠ 0) := by
  intro h
  have := certificate4977
  rw [h.1] at this
  norm_num at this
def C4978 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4978 : C4978.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4978 : ¬ (C4978.det = 0 ∧ ∀ i, C4978.adjugate i i ≠ 0) := by
  intro h
  have := certificate4978
  rw [h.1] at this
  norm_num at this
def C4979 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4979 : C4979.det = (23 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4979 : ¬ (C4979.det = 0 ∧ ∀ i, C4979.adjugate i i ≠ 0) := by
  intro h
  have := certificate4979
  rw [h.1] at this
  norm_num at this
def C4980 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4980 : C4980.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4980 : ¬ (C4980.det = 0 ∧ ∀ i, C4980.adjugate i i ≠ 0) := by
  intro h
  have := certificate4980
  rw [h.1] at this
  norm_num at this
def C4981 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4981 : C4981.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4981 : ¬ (C4981.det = 0 ∧ ∀ i, C4981.adjugate i i ≠ 0) := by
  intro h
  have := certificate4981
  rw [h.1] at this
  norm_num at this
def C4982 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4982 : C4982.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4982 : ¬ (C4982.det = 0 ∧ ∀ i, C4982.adjugate i i ≠ 0) := by
  intro h
  have := certificate4982
  rw [h.1] at this
  norm_num at this
def C4983 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4983 : C4983.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4983 : ¬ (C4983.det = 0 ∧ ∀ i, C4983.adjugate i i ≠ 0) := by
  intro h
  have := certificate4983
  rw [h.1] at this
  norm_num at this
def C4984 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4984 : C4984.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4984 : ¬ (C4984.det = 0 ∧ ∀ i, C4984.adjugate i i ≠ 0) := by
  intro h
  have := certificate4984
  rw [h.1] at this
  norm_num at this
def C4985 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4985 : C4985.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4985 : ¬ (C4985.det = 0 ∧ ∀ i, C4985.adjugate i i ≠ 0) := by
  intro h
  have := certificate4985
  rw [h.1] at this
  norm_num at this
def C4986 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4986 : C4986.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4986 : ¬ (C4986.det = 0 ∧ ∀ i, C4986.adjugate i i ≠ 0) := by
  intro h
  have := certificate4986
  rw [h.1] at this
  norm_num at this
def C4987 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4987 : C4987.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4987 : ¬ (C4987.det = 0 ∧ ∀ i, C4987.adjugate i i ≠ 0) := by
  intro h
  have := certificate4987
  rw [h.1] at this
  norm_num at this
def C4988 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4988 : C4988.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4988 : ¬ (C4988.det = 0 ∧ ∀ i, C4988.adjugate i i ≠ 0) := by
  intro h
  have := certificate4988
  rw [h.1] at this
  norm_num at this
def C4989 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate4989 : C4989.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4989 : ¬ (C4989.det = 0 ∧ ∀ i, C4989.adjugate i i ≠ 0) := by
  intro h
  have := certificate4989
  rw [h.1] at this
  norm_num at this
def C4990 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4990 : C4990.det = (49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4990 : ¬ (C4990.det = 0 ∧ ∀ i, C4990.adjugate i i ≠ 0) := by
  intro h
  have := certificate4990
  rw [h.1] at this
  norm_num at this
def C4991 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate4991 : C4991.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4991 : ¬ (C4991.det = 0 ∧ ∀ i, C4991.adjugate i i ≠ 0) := by
  intro h
  have := certificate4991
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0155
