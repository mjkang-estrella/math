import VerifiedDet
namespace Nut8.NewCertificates0113
def C3616 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3616 : C3616.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3616 : ¬ (C3616.det = 0 ∧ ∀ i, C3616.adjugate i i ≠ 0) := by
  intro h
  have := certificate3616
  rw [h.1] at this
  norm_num at this
def C3617 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3617 : C3617.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3617 : ¬ (C3617.det = 0 ∧ ∀ i, C3617.adjugate i i ≠ 0) := by
  intro h
  have := certificate3617
  rw [h.1] at this
  norm_num at this
def C3618 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3618 : C3618.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3618 : ¬ (C3618.det = 0 ∧ ∀ i, C3618.adjugate i i ≠ 0) := by
  intro h
  have := certificate3618
  rw [h.1] at this
  norm_num at this
def C3619 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3619 : C3619.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3619 : ¬ (C3619.det = 0 ∧ ∀ i, C3619.adjugate i i ≠ 0) := by
  intro h
  have := certificate3619
  rw [h.1] at this
  norm_num at this
def C3620 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3620 : C3620.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3620 : ¬ (C3620.det = 0 ∧ ∀ i, C3620.adjugate i i ≠ 0) := by
  intro h
  have := certificate3620
  rw [h.1] at this
  norm_num at this
def C3621 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3621 : C3621.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3621 : ¬ (C3621.det = 0 ∧ ∀ i, C3621.adjugate i i ≠ 0) := by
  intro h
  have := certificate3621
  rw [h.1] at this
  norm_num at this
def C3622 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3622 : C3622.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3622 : ¬ (C3622.det = 0 ∧ ∀ i, C3622.adjugate i i ≠ 0) := by
  intro h
  have := certificate3622
  rw [h.1] at this
  norm_num at this
def C3623 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3623 : C3623.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3623 : ¬ (C3623.det = 0 ∧ ∀ i, C3623.adjugate i i ≠ 0) := by
  intro h
  have := certificate3623
  rw [h.1] at this
  norm_num at this
def C3624 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3624 : C3624.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3624 : ¬ (C3624.det = 0 ∧ ∀ i, C3624.adjugate i i ≠ 0) := by
  intro h
  have := certificate3624
  rw [h.1] at this
  norm_num at this
def C3625 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3625 : C3625.det = (-61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3625 : ¬ (C3625.det = 0 ∧ ∀ i, C3625.adjugate i i ≠ 0) := by
  intro h
  have := certificate3625
  rw [h.1] at this
  norm_num at this
def C3626 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3626 : C3626.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3626 : ¬ (C3626.det = 0 ∧ ∀ i, C3626.adjugate i i ≠ 0) := by
  intro h
  have := certificate3626
  rw [h.1] at this
  norm_num at this
def C3627 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3627 : C3627.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3627 : ¬ (C3627.det = 0 ∧ ∀ i, C3627.adjugate i i ≠ 0) := by
  intro h
  have := certificate3627
  rw [h.1] at this
  norm_num at this
def C3628 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3628 : C3628.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3628 : ¬ (C3628.det = 0 ∧ ∀ i, C3628.adjugate i i ≠ 0) := by
  intro h
  have := certificate3628
  rw [h.1] at this
  norm_num at this
def C3629 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3629 : C3629.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3629 : ¬ (C3629.det = 0 ∧ ∀ i, C3629.adjugate i i ≠ 0) := by
  intro h
  have := certificate3629
  rw [h.1] at this
  norm_num at this
def C3630 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3630 : C3630.det = (-61 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3630 : ¬ (C3630.det = 0 ∧ ∀ i, C3630.adjugate i i ≠ 0) := by
  intro h
  have := certificate3630
  rw [h.1] at this
  norm_num at this
def C3631 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3631 : C3631.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3631 : ¬ (C3631.det = 0 ∧ ∀ i, C3631.adjugate i i ≠ 0) := by
  intro h
  have := certificate3631
  rw [h.1] at this
  norm_num at this
def C3632 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3632 : C3632.det = (39 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3632 : ¬ (C3632.det = 0 ∧ ∀ i, C3632.adjugate i i ≠ 0) := by
  intro h
  have := certificate3632
  rw [h.1] at this
  norm_num at this
def C3633 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0]
theorem certificate3633 : C3633.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3633 : ¬ (C3633.det = 0 ∧ ∀ i, C3633.adjugate i i ≠ 0) := by
  intro h
  have := certificate3633
  rw [h.1] at this
  norm_num at this
def C3634 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3634 : C3634.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3634 : ¬ (C3634.det = 0 ∧ ∀ i, C3634.adjugate i i ≠ 0) := by
  intro h
  have := certificate3634
  rw [h.1] at this
  norm_num at this
def C3635 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3635 : C3635.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3635 : ¬ (C3635.det = 0 ∧ ∀ i, C3635.adjugate i i ≠ 0) := by
  intro h
  have := certificate3635
  rw [h.1] at this
  norm_num at this
def C3636 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3636 : C3636.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3636 : ¬ (C3636.det = 0 ∧ ∀ i, C3636.adjugate i i ≠ 0) := by
  intro h
  have := certificate3636
  rw [h.1] at this
  norm_num at this
def C3637 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 2, 0, -1, 0]
theorem certificate3637 : C3637.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3637 : ¬ (C3637.det = 0 ∧ ∀ i, C3637.adjugate i i ≠ 0) := by
  intro h
  have := certificate3637
  rw [h.1] at this
  norm_num at this
def C3638 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3638 : C3638.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3638 : ¬ (C3638.det = 0 ∧ ∀ i, C3638.adjugate i i ≠ 0) := by
  intro h
  have := certificate3638
  rw [h.1] at this
  norm_num at this
def C3639 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3639 : C3639.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3639 : ¬ (C3639.det = 0 ∧ ∀ i, C3639.adjugate i i ≠ 0) := by
  intro h
  have := certificate3639
  rw [h.1] at this
  norm_num at this
def C3640 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3640 : C3640.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3640 : ¬ (C3640.det = 0 ∧ ∀ i, C3640.adjugate i i ≠ 0) := by
  intro h
  have := certificate3640
  rw [h.1] at this
  norm_num at this
def C3641 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3641 : C3641.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3641 : ¬ (C3641.det = 0 ∧ ∀ i, C3641.adjugate i i ≠ 0) := by
  intro h
  have := certificate3641
  rw [h.1] at this
  norm_num at this
def C3642 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3642 : C3642.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3642 : ¬ (C3642.det = 0 ∧ ∀ i, C3642.adjugate i i ≠ 0) := by
  intro h
  have := certificate3642
  rw [h.1] at this
  norm_num at this
def C3643 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3643 : C3643.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3643 : ¬ (C3643.det = 0 ∧ ∀ i, C3643.adjugate i i ≠ 0) := by
  intro h
  have := certificate3643
  rw [h.1] at this
  norm_num at this
def C3644 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate3644 : C3644.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3644 : ¬ (C3644.det = 0 ∧ ∀ i, C3644.adjugate i i ≠ 0) := by
  intro h
  have := certificate3644
  rw [h.1] at this
  norm_num at this
def C3645 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate3645 : C3645.det = (-14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3645 : ¬ (C3645.det = 0 ∧ ∀ i, C3645.adjugate i i ≠ 0) := by
  intro h
  have := certificate3645
  rw [h.1] at this
  norm_num at this
def C3646 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate3646 : C3646.det = (-46 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3646 : ¬ (C3646.det = 0 ∧ ∀ i, C3646.adjugate i i ≠ 0) := by
  intro h
  have := certificate3646
  rw [h.1] at this
  norm_num at this
def C3647 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate3647 : C3647.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3647 : ¬ (C3647.det = 0 ∧ ∀ i, C3647.adjugate i i ≠ 0) := by
  intro h
  have := certificate3647
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0113
