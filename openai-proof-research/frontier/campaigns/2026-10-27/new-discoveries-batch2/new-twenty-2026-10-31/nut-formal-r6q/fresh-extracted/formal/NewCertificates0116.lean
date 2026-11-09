import VerifiedDet
namespace Nut8.NewCertificates0116
def C3712 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3712 : C3712.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3712 : ¬ (C3712.det = 0 ∧ ∀ i, C3712.adjugate i i ≠ 0) := by
  intro h
  have := certificate3712
  rw [h.1] at this
  norm_num at this
def C3713 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate3713 : C3713.det = (-49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3713 : ¬ (C3713.det = 0 ∧ ∀ i, C3713.adjugate i i ≠ 0) := by
  intro h
  have := certificate3713
  rw [h.1] at this
  norm_num at this
def C3714 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3714 : C3714.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3714 : ¬ (C3714.det = 0 ∧ ∀ i, C3714.adjugate i i ≠ 0) := by
  intro h
  have := certificate3714
  rw [h.1] at this
  norm_num at this
def C3715 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3715 : C3715.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3715 : ¬ (C3715.det = 0 ∧ ∀ i, C3715.adjugate i i ≠ 0) := by
  intro h
  have := certificate3715
  rw [h.1] at this
  norm_num at this
def C3716 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3716 : C3716.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3716 : ¬ (C3716.det = 0 ∧ ∀ i, C3716.adjugate i i ≠ 0) := by
  intro h
  have := certificate3716
  rw [h.1] at this
  norm_num at this
def C3717 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate3717 : C3717.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3717 : ¬ (C3717.det = 0 ∧ ∀ i, C3717.adjugate i i ≠ 0) := by
  intro h
  have := certificate3717
  rw [h.1] at this
  norm_num at this
def C3718 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3718 : C3718.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3718 : ¬ (C3718.det = 0 ∧ ∀ i, C3718.adjugate i i ≠ 0) := by
  intro h
  have := certificate3718
  rw [h.1] at this
  norm_num at this
def C3719 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3719 : C3719.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3719 : ¬ (C3719.det = 0 ∧ ∀ i, C3719.adjugate i i ≠ 0) := by
  intro h
  have := certificate3719
  rw [h.1] at this
  norm_num at this
def C3720 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3720 : C3720.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3720 : ¬ (C3720.det = 0 ∧ ∀ i, C3720.adjugate i i ≠ 0) := by
  intro h
  have := certificate3720
  rw [h.1] at this
  norm_num at this
def C3721 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3721 : C3721.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3721 : ¬ (C3721.det = 0 ∧ ∀ i, C3721.adjugate i i ≠ 0) := by
  intro h
  have := certificate3721
  rw [h.1] at this
  norm_num at this
def C3722 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3722 : C3722.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3722 : ¬ (C3722.det = 0 ∧ ∀ i, C3722.adjugate i i ≠ 0) := by
  intro h
  have := certificate3722
  rw [h.1] at this
  norm_num at this
def C3723 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3723 : C3723.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3723 : ¬ (C3723.det = 0 ∧ ∀ i, C3723.adjugate i i ≠ 0) := by
  intro h
  have := certificate3723
  rw [h.1] at this
  norm_num at this
def C3724 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3724 : C3724.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3724 : ¬ (C3724.det = 0 ∧ ∀ i, C3724.adjugate i i ≠ 0) := by
  intro h
  have := certificate3724
  rw [h.1] at this
  norm_num at this
def C3725 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3725 : C3725.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3725 : ¬ (C3725.det = 0 ∧ ∀ i, C3725.adjugate i i ≠ 0) := by
  intro h
  have := certificate3725
  rw [h.1] at this
  norm_num at this
def C3726 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3726 : C3726.det = (-49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3726 : ¬ (C3726.det = 0 ∧ ∀ i, C3726.adjugate i i ≠ 0) := by
  intro h
  have := certificate3726
  rw [h.1] at this
  norm_num at this
def C3727 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3727 : C3727.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3727 : ¬ (C3727.det = 0 ∧ ∀ i, C3727.adjugate i i ≠ 0) := by
  intro h
  have := certificate3727
  rw [h.1] at this
  norm_num at this
def C3728 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3728 : C3728.det = (51 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3728 : ¬ (C3728.det = 0 ∧ ∀ i, C3728.adjugate i i ≠ 0) := by
  intro h
  have := certificate3728
  rw [h.1] at this
  norm_num at this
def C3729 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate3729 : C3729.det = (-49 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3729 : ¬ (C3729.det = 0 ∧ ∀ i, C3729.adjugate i i ≠ 0) := by
  intro h
  have := certificate3729
  rw [h.1] at this
  norm_num at this
def C3730 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3730 : C3730.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3730 : ¬ (C3730.det = 0 ∧ ∀ i, C3730.adjugate i i ≠ 0) := by
  intro h
  have := certificate3730
  rw [h.1] at this
  norm_num at this
def C3731 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3731 : C3731.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3731 : ¬ (C3731.det = 0 ∧ ∀ i, C3731.adjugate i i ≠ 0) := by
  intro h
  have := certificate3731
  rw [h.1] at this
  norm_num at this
def C3732 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3732 : C3732.det = (43 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3732 : ¬ (C3732.det = 0 ∧ ∀ i, C3732.adjugate i i ≠ 0) := by
  intro h
  have := certificate3732
  rw [h.1] at this
  norm_num at this
def C3733 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate3733 : C3733.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3733 : ¬ (C3733.det = 0 ∧ ∀ i, C3733.adjugate i i ≠ 0) := by
  intro h
  have := certificate3733
  rw [h.1] at this
  norm_num at this
def C3734 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3734 : C3734.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3734 : ¬ (C3734.det = 0 ∧ ∀ i, C3734.adjugate i i ≠ 0) := by
  intro h
  have := certificate3734
  rw [h.1] at this
  norm_num at this
def C3735 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3735 : C3735.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3735 : ¬ (C3735.det = 0 ∧ ∀ i, C3735.adjugate i i ≠ 0) := by
  intro h
  have := certificate3735
  rw [h.1] at this
  norm_num at this
def C3736 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3736 : C3736.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3736 : ¬ (C3736.det = 0 ∧ ∀ i, C3736.adjugate i i ≠ 0) := by
  intro h
  have := certificate3736
  rw [h.1] at this
  norm_num at this
def C3737 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate3737 : C3737.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3737 : ¬ (C3737.det = 0 ∧ ∀ i, C3737.adjugate i i ≠ 0) := by
  intro h
  have := certificate3737
  rw [h.1] at this
  norm_num at this
def C3738 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3738 : C3738.det = (-31 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3738 : ¬ (C3738.det = 0 ∧ ∀ i, C3738.adjugate i i ≠ 0) := by
  intro h
  have := certificate3738
  rw [h.1] at this
  norm_num at this
def C3739 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3739 : C3739.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3739 : ¬ (C3739.det = 0 ∧ ∀ i, C3739.adjugate i i ≠ 0) := by
  intro h
  have := certificate3739
  rw [h.1] at this
  norm_num at this
def C3740 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3740 : C3740.det = (21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3740 : ¬ (C3740.det = 0 ∧ ∀ i, C3740.adjugate i i ≠ 0) := by
  intro h
  have := certificate3740
  rw [h.1] at this
  norm_num at this
def C3741 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate3741 : C3741.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3741 : ¬ (C3741.det = 0 ∧ ∀ i, C3741.adjugate i i ≠ 0) := by
  intro h
  have := certificate3741
  rw [h.1] at this
  norm_num at this
def C3742 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3742 : C3742.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3742 : ¬ (C3742.det = 0 ∧ ∀ i, C3742.adjugate i i ≠ 0) := by
  intro h
  have := certificate3742
  rw [h.1] at this
  norm_num at this
def C3743 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate3743 : C3743.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction3743 : ¬ (C3743.det = 0 ∧ ∀ i, C3743.adjugate i i ≠ 0) := by
  intro h
  have := certificate3743
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0116
