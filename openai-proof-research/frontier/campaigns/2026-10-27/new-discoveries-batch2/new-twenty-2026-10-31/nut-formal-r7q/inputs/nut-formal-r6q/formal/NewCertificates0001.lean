import VerifiedDet
namespace Nut8.NewCertificates0001
def C32 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate32 : C32.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction32 : ¬ (C32.det = 0 ∧ ∀ i, C32.adjugate i i ≠ 0) := by
  intro h
  have := certificate32
  rw [h.1] at this
  norm_num at this
def C33 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate33 : C33.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction33 : ¬ (C33.det = 0 ∧ ∀ i, C33.adjugate i i ≠ 0) := by
  intro h
  have := certificate33
  rw [h.1] at this
  norm_num at this
def C34 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate34 : C34.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction34 : ¬ (C34.det = 0 ∧ ∀ i, C34.adjugate i i ≠ 0) := by
  intro h
  have := certificate34
  rw [h.1] at this
  norm_num at this
def C35 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate35 : C35.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction35 : ¬ (C35.det = 0 ∧ ∀ i, C35.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate35
def C36 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate36 : C36.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction36 : ¬ (C36.det = 0 ∧ ∀ i, C36.adjugate i i ≠ 0) := by
  intro h
  have := certificate36
  rw [h.1] at this
  norm_num at this
def C37 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate37 : C37.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction37 : ¬ (C37.det = 0 ∧ ∀ i, C37.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate37
def C38 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate38 : C38.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction38 : ¬ (C38.det = 0 ∧ ∀ i, C38.adjugate i i ≠ 0) := by
  intro h
  have := certificate38
  rw [h.1] at this
  norm_num at this
def C39 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate39 : C39.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction39 : ¬ (C39.det = 0 ∧ ∀ i, C39.adjugate i i ≠ 0) := by
  intro h
  have := certificate39
  rw [h.1] at this
  norm_num at this
def C40 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate40 : C40.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction40 : ¬ (C40.det = 0 ∧ ∀ i, C40.adjugate i i ≠ 0) := by
  intro h
  have := certificate40
  rw [h.1] at this
  norm_num at this
def C41 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate41 : C41.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction41 : ¬ (C41.det = 0 ∧ ∀ i, C41.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate41
def C42 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate42 : C42.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction42 : ¬ (C42.det = 0 ∧ ∀ i, C42.adjugate i i ≠ 0) := by
  intro h
  have := certificate42
  rw [h.1] at this
  norm_num at this
def C43 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate43 : C43.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction43 : ¬ (C43.det = 0 ∧ ∀ i, C43.adjugate i i ≠ 0) := by
  intro h
  have := certificate43
  rw [h.1] at this
  norm_num at this
def C44 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate44 : C44.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction44 : ¬ (C44.det = 0 ∧ ∀ i, C44.adjugate i i ≠ 0) := by
  intro h
  have := certificate44
  rw [h.1] at this
  norm_num at this
def C45 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate45 : C45.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction45 : ¬ (C45.det = 0 ∧ ∀ i, C45.adjugate i i ≠ 0) := by
  intro h
  have := certificate45
  rw [h.1] at this
  norm_num at this
def C46 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate46 : C46.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction46 : ¬ (C46.det = 0 ∧ ∀ i, C46.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate46
def C47 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate47 : C47.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction47 : ¬ (C47.det = 0 ∧ ∀ i, C47.adjugate i i ≠ 0) := by
  intro h
  have := certificate47
  rw [h.1] at this
  norm_num at this
def C48 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate48 : C48.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction48 : ¬ (C48.det = 0 ∧ ∀ i, C48.adjugate i i ≠ 0) := by
  intro h
  have := certificate48
  rw [h.1] at this
  norm_num at this
def C49 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate49 : C49.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction49 : ¬ (C49.det = 0 ∧ ∀ i, C49.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate49
def C50 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate50 : C50.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction50 : ¬ (C50.det = 0 ∧ ∀ i, C50.adjugate i i ≠ 0) := by
  intro h
  have := certificate50
  rw [h.1] at this
  norm_num at this
def C51 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate51 : C51.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction51 : ¬ (C51.det = 0 ∧ ∀ i, C51.adjugate i i ≠ 0) := by
  intro h
  have := certificate51
  rw [h.1] at this
  norm_num at this
def C52 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate52 : C52.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction52 : ¬ (C52.det = 0 ∧ ∀ i, C52.adjugate i i ≠ 0) := by
  intro h
  have := certificate52
  rw [h.1] at this
  norm_num at this
def C53 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate53 : C53.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction53 : ¬ (C53.det = 0 ∧ ∀ i, C53.adjugate i i ≠ 0) := by
  intro h
  have := certificate53
  rw [h.1] at this
  norm_num at this
def C54 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate54 : C54.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction54 : ¬ (C54.det = 0 ∧ ∀ i, C54.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate54
def C55 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate55 : C55.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction55 : ¬ (C55.det = 0 ∧ ∀ i, C55.adjugate i i ≠ 0) := by
  intro h
  have := certificate55
  rw [h.1] at this
  norm_num at this
def C56 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate56 : C56.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction56 : ¬ (C56.det = 0 ∧ ∀ i, C56.adjugate i i ≠ 0) := by
  intro h
  have := certificate56
  rw [h.1] at this
  norm_num at this
def C57 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate57 : C57.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction57 : ¬ (C57.det = 0 ∧ ∀ i, C57.adjugate i i ≠ 0) := by
  intro h
  have := certificate57
  rw [h.1] at this
  norm_num at this
def C58 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate58 : C58.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction58 : ¬ (C58.det = 0 ∧ ∀ i, C58.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate58
def C59 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate59 : C59.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction59 : ¬ (C59.det = 0 ∧ ∀ i, C59.adjugate i i ≠ 0) := by
  intro h
  have := certificate59
  rw [h.1] at this
  norm_num at this
def C60 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate60 : C60.adjugate 4 4 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction60 : ¬ (C60.det = 0 ∧ ∀ i, C60.adjugate i i ≠ 0) := by
  intro h
  exact h.2 4 certificate60
def C61 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate61 : C61.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction61 : ¬ (C61.det = 0 ∧ ∀ i, C61.adjugate i i ≠ 0) := by
  intro h
  have := certificate61
  rw [h.1] at this
  norm_num at this
def C62 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate62 : C62.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction62 : ¬ (C62.det = 0 ∧ ∀ i, C62.adjugate i i ≠ 0) := by
  intro h
  have := certificate62
  rw [h.1] at this
  norm_num at this
def C63 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate63 : C63.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction63 : ¬ (C63.det = 0 ∧ ∀ i, C63.adjugate i i ≠ 0) := by
  intro h
  have := certificate63
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0001
