import VerifiedDet
namespace Nut8.NewCertificates0115
def C3680 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate3680 : C3680.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3680 : ¬ (C3680.det = 0 ∧ ∀ i, C3680.adjugate i i ≠ 0) := by
  intro h
  have := certificate3680
  rw [h.1] at this
  norm_num at this
def C3681 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate3681 : C3681.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3681 : ¬ (C3681.det = 0 ∧ ∀ i, C3681.adjugate i i ≠ 0) := by
  intro h
  have := certificate3681
  rw [h.1] at this
  norm_num at this
def C3682 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3682 : C3682.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3682 : ¬ (C3682.det = 0 ∧ ∀ i, C3682.adjugate i i ≠ 0) := by
  intro h
  have := certificate3682
  rw [h.1] at this
  norm_num at this
def C3683 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3683 : C3683.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3683 : ¬ (C3683.det = 0 ∧ ∀ i, C3683.adjugate i i ≠ 0) := by
  intro h
  have := certificate3683
  rw [h.1] at this
  norm_num at this
def C3684 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate3684 : C3684.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3684 : ¬ (C3684.det = 0 ∧ ∀ i, C3684.adjugate i i ≠ 0) := by
  intro h
  have := certificate3684
  rw [h.1] at this
  norm_num at this
def C3685 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate3685 : C3685.det = (-33 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3685 : ¬ (C3685.det = 0 ∧ ∀ i, C3685.adjugate i i ≠ 0) := by
  intro h
  have := certificate3685
  rw [h.1] at this
  norm_num at this
def C3686 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3686 : C3686.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3686 : ¬ (C3686.det = 0 ∧ ∀ i, C3686.adjugate i i ≠ 0) := by
  intro h
  have := certificate3686
  rw [h.1] at this
  norm_num at this
def C3687 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3687 : C3687.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3687 : ¬ (C3687.det = 0 ∧ ∀ i, C3687.adjugate i i ≠ 0) := by
  intro h
  have := certificate3687
  rw [h.1] at this
  norm_num at this
def C3688 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3688 : C3688.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3688 : ¬ (C3688.det = 0 ∧ ∀ i, C3688.adjugate i i ≠ 0) := by
  intro h
  have := certificate3688
  rw [h.1] at this
  norm_num at this
def C3689 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3689 : C3689.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3689 : ¬ (C3689.det = 0 ∧ ∀ i, C3689.adjugate i i ≠ 0) := by
  intro h
  have := certificate3689
  rw [h.1] at this
  norm_num at this
def C3690 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3690 : C3690.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3690 : ¬ (C3690.det = 0 ∧ ∀ i, C3690.adjugate i i ≠ 0) := by
  intro h
  have := certificate3690
  rw [h.1] at this
  norm_num at this
def C3691 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3691 : C3691.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3691 : ¬ (C3691.det = 0 ∧ ∀ i, C3691.adjugate i i ≠ 0) := by
  intro h
  have := certificate3691
  rw [h.1] at this
  norm_num at this
def C3692 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3692 : C3692.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3692 : ¬ (C3692.det = 0 ∧ ∀ i, C3692.adjugate i i ≠ 0) := by
  intro h
  have := certificate3692
  rw [h.1] at this
  norm_num at this
def C3693 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3693 : C3693.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3693 : ¬ (C3693.det = 0 ∧ ∀ i, C3693.adjugate i i ≠ 0) := by
  intro h
  have := certificate3693
  rw [h.1] at this
  norm_num at this
def C3694 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3694 : C3694.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3694 : ¬ (C3694.det = 0 ∧ ∀ i, C3694.adjugate i i ≠ 0) := by
  intro h
  have := certificate3694
  rw [h.1] at this
  norm_num at this
def C3695 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3695 : C3695.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3695 : ¬ (C3695.det = 0 ∧ ∀ i, C3695.adjugate i i ≠ 0) := by
  intro h
  have := certificate3695
  rw [h.1] at this
  norm_num at this
def C3696 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate3696 : C3696.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3696 : ¬ (C3696.det = 0 ∧ ∀ i, C3696.adjugate i i ≠ 0) := by
  intro h
  have := certificate3696
  rw [h.1] at this
  norm_num at this
def C3697 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate3697 : C3697.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3697 : ¬ (C3697.det = 0 ∧ ∀ i, C3697.adjugate i i ≠ 0) := by
  intro h
  have := certificate3697
  rw [h.1] at this
  norm_num at this
def C3698 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3698 : C3698.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3698 : ¬ (C3698.det = 0 ∧ ∀ i, C3698.adjugate i i ≠ 0) := by
  intro h
  have := certificate3698
  rw [h.1] at this
  norm_num at this
def C3699 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3699 : C3699.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3699 : ¬ (C3699.det = 0 ∧ ∀ i, C3699.adjugate i i ≠ 0) := by
  intro h
  have := certificate3699
  rw [h.1] at this
  norm_num at this
def C3700 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate3700 : C3700.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3700 : ¬ (C3700.det = 0 ∧ ∀ i, C3700.adjugate i i ≠ 0) := by
  intro h
  have := certificate3700
  rw [h.1] at this
  norm_num at this
def C3701 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate3701 : C3701.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3701 : ¬ (C3701.det = 0 ∧ ∀ i, C3701.adjugate i i ≠ 0) := by
  intro h
  have := certificate3701
  rw [h.1] at this
  norm_num at this
def C3702 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3702 : C3702.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3702 : ¬ (C3702.det = 0 ∧ ∀ i, C3702.adjugate i i ≠ 0) := by
  intro h
  have := certificate3702
  rw [h.1] at this
  norm_num at this
def C3703 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3703 : C3703.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3703 : ¬ (C3703.det = 0 ∧ ∀ i, C3703.adjugate i i ≠ 0) := by
  intro h
  have := certificate3703
  rw [h.1] at this
  norm_num at this
def C3704 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3704 : C3704.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3704 : ¬ (C3704.det = 0 ∧ ∀ i, C3704.adjugate i i ≠ 0) := by
  intro h
  have := certificate3704
  rw [h.1] at this
  norm_num at this
def C3705 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3705 : C3705.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3705 : ¬ (C3705.det = 0 ∧ ∀ i, C3705.adjugate i i ≠ 0) := by
  intro h
  have := certificate3705
  rw [h.1] at this
  norm_num at this
def C3706 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3706 : C3706.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3706 : ¬ (C3706.det = 0 ∧ ∀ i, C3706.adjugate i i ≠ 0) := by
  intro h
  have := certificate3706
  rw [h.1] at this
  norm_num at this
def C3707 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3707 : C3707.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3707 : ¬ (C3707.det = 0 ∧ ∀ i, C3707.adjugate i i ≠ 0) := by
  intro h
  have := certificate3707
  rw [h.1] at this
  norm_num at this
def C3708 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3708 : C3708.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3708 : ¬ (C3708.det = 0 ∧ ∀ i, C3708.adjugate i i ≠ 0) := by
  intro h
  have := certificate3708
  rw [h.1] at this
  norm_num at this
def C3709 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3709 : C3709.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3709 : ¬ (C3709.det = 0 ∧ ∀ i, C3709.adjugate i i ≠ 0) := by
  intro h
  have := certificate3709
  rw [h.1] at this
  norm_num at this
def C3710 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3710 : C3710.det = (-49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3710 : ¬ (C3710.det = 0 ∧ ∀ i, C3710.adjugate i i ≠ 0) := by
  intro h
  have := certificate3710
  rw [h.1] at this
  norm_num at this
def C3711 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3711 : C3711.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3711 : ¬ (C3711.det = 0 ∧ ∀ i, C3711.adjugate i i ≠ 0) := by
  intro h
  have := certificate3711
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0115
