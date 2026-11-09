import VerifiedDet
namespace Nut8.NewCertificates0188
def C6016 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6016 : C6016.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6016 : ¬ (C6016.det = 0 ∧ ∀ i, C6016.adjugate i i ≠ 0) := by
  intro h
  have := certificate6016
  rw [h.1] at this
  norm_num at this
def C6017 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6017 : C6017.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6017 : ¬ (C6017.det = 0 ∧ ∀ i, C6017.adjugate i i ≠ 0) := by
  intro h
  have := certificate6017
  rw [h.1] at this
  norm_num at this
def C6018 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6018 : C6018.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6018 : ¬ (C6018.det = 0 ∧ ∀ i, C6018.adjugate i i ≠ 0) := by
  intro h
  have := certificate6018
  rw [h.1] at this
  norm_num at this
def C6019 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6019 : C6019.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6019 : ¬ (C6019.det = 0 ∧ ∀ i, C6019.adjugate i i ≠ 0) := by
  intro h
  have := certificate6019
  rw [h.1] at this
  norm_num at this
def C6020 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate6020 : C6020.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6020 : ¬ (C6020.det = 0 ∧ ∀ i, C6020.adjugate i i ≠ 0) := by
  intro h
  have := certificate6020
  rw [h.1] at this
  norm_num at this
def C6021 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate6021 : C6021.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6021 : ¬ (C6021.det = 0 ∧ ∀ i, C6021.adjugate i i ≠ 0) := by
  intro h
  have := certificate6021
  rw [h.1] at this
  norm_num at this
def C6022 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate6022 : C6022.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6022 : ¬ (C6022.det = 0 ∧ ∀ i, C6022.adjugate i i ≠ 0) := by
  intro h
  have := certificate6022
  rw [h.1] at this
  norm_num at this
def C6023 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate6023 : C6023.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6023 : ¬ (C6023.det = 0 ∧ ∀ i, C6023.adjugate i i ≠ 0) := by
  intro h
  have := certificate6023
  rw [h.1] at this
  norm_num at this
def C6024 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate6024 : C6024.det = (-47 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6024 : ¬ (C6024.det = 0 ∧ ∀ i, C6024.adjugate i i ≠ 0) := by
  intro h
  have := certificate6024
  rw [h.1] at this
  norm_num at this
def C6025 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate6025 : C6025.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6025 : ¬ (C6025.det = 0 ∧ ∀ i, C6025.adjugate i i ≠ 0) := by
  intro h
  have := certificate6025
  rw [h.1] at this
  norm_num at this
def C6026 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate6026 : C6026.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6026 : ¬ (C6026.det = 0 ∧ ∀ i, C6026.adjugate i i ≠ 0) := by
  intro h
  have := certificate6026
  rw [h.1] at this
  norm_num at this
def C6027 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate6027 : C6027.det = (33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6027 : ¬ (C6027.det = 0 ∧ ∀ i, C6027.adjugate i i ≠ 0) := by
  intro h
  have := certificate6027
  rw [h.1] at this
  norm_num at this
def C6028 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6028 : C6028.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6028 : ¬ (C6028.det = 0 ∧ ∀ i, C6028.adjugate i i ≠ 0) := by
  intro h
  have := certificate6028
  rw [h.1] at this
  norm_num at this
def C6029 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6029 : C6029.det = (-56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6029 : ¬ (C6029.det = 0 ∧ ∀ i, C6029.adjugate i i ≠ 0) := by
  intro h
  have := certificate6029
  rw [h.1] at this
  norm_num at this
def C6030 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6030 : C6030.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6030 : ¬ (C6030.det = 0 ∧ ∀ i, C6030.adjugate i i ≠ 0) := by
  intro h
  have := certificate6030
  rw [h.1] at this
  norm_num at this
def C6031 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6031 : C6031.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6031 : ¬ (C6031.det = 0 ∧ ∀ i, C6031.adjugate i i ≠ 0) := by
  intro h
  have := certificate6031
  rw [h.1] at this
  norm_num at this
def C6032 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate6032 : C6032.det = (-56 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6032 : ¬ (C6032.det = 0 ∧ ∀ i, C6032.adjugate i i ≠ 0) := by
  intro h
  have := certificate6032
  rw [h.1] at this
  norm_num at this
def C6033 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate6033 : C6033.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6033 : ¬ (C6033.det = 0 ∧ ∀ i, C6033.adjugate i i ≠ 0) := by
  intro h
  have := certificate6033
  rw [h.1] at this
  norm_num at this
def C6034 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate6034 : C6034.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6034 : ¬ (C6034.det = 0 ∧ ∀ i, C6034.adjugate i i ≠ 0) := by
  intro h
  have := certificate6034
  rw [h.1] at this
  norm_num at this
def C6035 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate6035 : C6035.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6035 : ¬ (C6035.det = 0 ∧ ∀ i, C6035.adjugate i i ≠ 0) := by
  intro h
  have := certificate6035
  rw [h.1] at this
  norm_num at this
def C6036 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6036 : C6036.det = (-27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6036 : ¬ (C6036.det = 0 ∧ ∀ i, C6036.adjugate i i ≠ 0) := by
  intro h
  have := certificate6036
  rw [h.1] at this
  norm_num at this
def C6037 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6037 : C6037.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6037 : ¬ (C6037.det = 0 ∧ ∀ i, C6037.adjugate i i ≠ 0) := by
  intro h
  have := certificate6037
  rw [h.1] at this
  norm_num at this
def C6038 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6038 : C6038.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6038 : ¬ (C6038.det = 0 ∧ ∀ i, C6038.adjugate i i ≠ 0) := by
  intro h
  have := certificate6038
  rw [h.1] at this
  norm_num at this
def C6039 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6039 : C6039.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6039 : ¬ (C6039.det = 0 ∧ ∀ i, C6039.adjugate i i ≠ 0) := by
  intro h
  have := certificate6039
  rw [h.1] at this
  norm_num at this
def C6040 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6040 : C6040.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6040 : ¬ (C6040.det = 0 ∧ ∀ i, C6040.adjugate i i ≠ 0) := by
  intro h
  have := certificate6040
  rw [h.1] at this
  norm_num at this
def C6041 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6041 : C6041.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6041 : ¬ (C6041.det = 0 ∧ ∀ i, C6041.adjugate i i ≠ 0) := by
  intro h
  have := certificate6041
  rw [h.1] at this
  norm_num at this
def C6042 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6042 : C6042.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6042 : ¬ (C6042.det = 0 ∧ ∀ i, C6042.adjugate i i ≠ 0) := by
  intro h
  have := certificate6042
  rw [h.1] at this
  norm_num at this
def C6043 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 1, 0; 0, 1, 0, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, -1, 0, 0; 0, 0, 1, 1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6043 : C6043.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6043 : ¬ (C6043.det = 0 ∧ ∀ i, C6043.adjugate i i ≠ 0) := by
  intro h
  have := certificate6043
  rw [h.1] at this
  norm_num at this
def C6044 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6044 : C6044.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6044 : ¬ (C6044.det = 0 ∧ ∀ i, C6044.adjugate i i ≠ 0) := by
  intro h
  have := certificate6044
  rw [h.1] at this
  norm_num at this
def C6045 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6045 : C6045.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6045 : ¬ (C6045.det = 0 ∧ ∀ i, C6045.adjugate i i ≠ 0) := by
  intro h
  have := certificate6045
  rw [h.1] at this
  norm_num at this
def C6046 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6046 : C6046.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6046 : ¬ (C6046.det = 0 ∧ ∀ i, C6046.adjugate i i ≠ 0) := by
  intro h
  have := certificate6046
  rw [h.1] at this
  norm_num at this
def C6047 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, -1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6047 : C6047.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6047 : ¬ (C6047.det = 0 ∧ ∀ i, C6047.adjugate i i ≠ 0) := by
  intro h
  have := certificate6047
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0188
