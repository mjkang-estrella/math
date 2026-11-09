import VerifiedDet
namespace Nut8.NewCertificates0145
def C4640 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4640 : C4640.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4640 : ¬ (C4640.det = 0 ∧ ∀ i, C4640.adjugate i i ≠ 0) := by
  intro h
  have := certificate4640
  rw [h.1] at this
  norm_num at this
def C4641 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4641 : C4641.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4641 : ¬ (C4641.det = 0 ∧ ∀ i, C4641.adjugate i i ≠ 0) := by
  intro h
  have := certificate4641
  rw [h.1] at this
  norm_num at this
def C4642 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4642 : C4642.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4642 : ¬ (C4642.det = 0 ∧ ∀ i, C4642.adjugate i i ≠ 0) := by
  intro h
  have := certificate4642
  rw [h.1] at this
  norm_num at this
def C4643 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4643 : C4643.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4643 : ¬ (C4643.det = 0 ∧ ∀ i, C4643.adjugate i i ≠ 0) := by
  intro h
  have := certificate4643
  rw [h.1] at this
  norm_num at this
def C4644 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4644 : C4644.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4644 : ¬ (C4644.det = 0 ∧ ∀ i, C4644.adjugate i i ≠ 0) := by
  intro h
  have := certificate4644
  rw [h.1] at this
  norm_num at this
def C4645 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4645 : C4645.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4645 : ¬ (C4645.det = 0 ∧ ∀ i, C4645.adjugate i i ≠ 0) := by
  intro h
  have := certificate4645
  rw [h.1] at this
  norm_num at this
def C4646 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4646 : C4646.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4646 : ¬ (C4646.det = 0 ∧ ∀ i, C4646.adjugate i i ≠ 0) := by
  intro h
  have := certificate4646
  rw [h.1] at this
  norm_num at this
def C4647 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4647 : C4647.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4647 : ¬ (C4647.det = 0 ∧ ∀ i, C4647.adjugate i i ≠ 0) := by
  intro h
  have := certificate4647
  rw [h.1] at this
  norm_num at this
def C4648 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4648 : C4648.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4648 : ¬ (C4648.det = 0 ∧ ∀ i, C4648.adjugate i i ≠ 0) := by
  intro h
  have := certificate4648
  rw [h.1] at this
  norm_num at this
def C4649 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4649 : C4649.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4649 : ¬ (C4649.det = 0 ∧ ∀ i, C4649.adjugate i i ≠ 0) := by
  intro h
  have := certificate4649
  rw [h.1] at this
  norm_num at this
def C4650 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4650 : C4650.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4650 : ¬ (C4650.det = 0 ∧ ∀ i, C4650.adjugate i i ≠ 0) := by
  intro h
  have := certificate4650
  rw [h.1] at this
  norm_num at this
def C4651 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4651 : C4651.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4651 : ¬ (C4651.det = 0 ∧ ∀ i, C4651.adjugate i i ≠ 0) := by
  intro h
  have := certificate4651
  rw [h.1] at this
  norm_num at this
def C4652 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4652 : C4652.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4652 : ¬ (C4652.det = 0 ∧ ∀ i, C4652.adjugate i i ≠ 0) := by
  intro h
  have := certificate4652
  rw [h.1] at this
  norm_num at this
def C4653 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4653 : C4653.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4653 : ¬ (C4653.det = 0 ∧ ∀ i, C4653.adjugate i i ≠ 0) := by
  intro h
  have := certificate4653
  rw [h.1] at this
  norm_num at this
def C4654 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4654 : C4654.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4654 : ¬ (C4654.det = 0 ∧ ∀ i, C4654.adjugate i i ≠ 0) := by
  intro h
  have := certificate4654
  rw [h.1] at this
  norm_num at this
def C4655 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4655 : C4655.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4655 : ¬ (C4655.det = 0 ∧ ∀ i, C4655.adjugate i i ≠ 0) := by
  intro h
  have := certificate4655
  rw [h.1] at this
  norm_num at this
def C4656 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4656 : C4656.det = (-11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4656 : ¬ (C4656.det = 0 ∧ ∀ i, C4656.adjugate i i ≠ 0) := by
  intro h
  have := certificate4656
  rw [h.1] at this
  norm_num at this
def C4657 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4657 : C4657.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4657 : ¬ (C4657.det = 0 ∧ ∀ i, C4657.adjugate i i ≠ 0) := by
  intro h
  have := certificate4657
  rw [h.1] at this
  norm_num at this
def C4658 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4658 : C4658.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4658 : ¬ (C4658.det = 0 ∧ ∀ i, C4658.adjugate i i ≠ 0) := by
  intro h
  have := certificate4658
  rw [h.1] at this
  norm_num at this
def C4659 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4659 : C4659.det = (17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4659 : ¬ (C4659.det = 0 ∧ ∀ i, C4659.adjugate i i ≠ 0) := by
  intro h
  have := certificate4659
  rw [h.1] at this
  norm_num at this
def C4660 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4660 : C4660.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4660 : ¬ (C4660.det = 0 ∧ ∀ i, C4660.adjugate i i ≠ 0) := by
  intro h
  have := certificate4660
  rw [h.1] at this
  norm_num at this
def C4661 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4661 : C4661.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4661 : ¬ (C4661.det = 0 ∧ ∀ i, C4661.adjugate i i ≠ 0) := by
  intro h
  have := certificate4661
  rw [h.1] at this
  norm_num at this
def C4662 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4662 : C4662.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4662 : ¬ (C4662.det = 0 ∧ ∀ i, C4662.adjugate i i ≠ 0) := by
  intro h
  have := certificate4662
  rw [h.1] at this
  norm_num at this
def C4663 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4663 : C4663.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4663 : ¬ (C4663.det = 0 ∧ ∀ i, C4663.adjugate i i ≠ 0) := by
  intro h
  have := certificate4663
  rw [h.1] at this
  norm_num at this
def C4664 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4664 : C4664.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4664 : ¬ (C4664.det = 0 ∧ ∀ i, C4664.adjugate i i ≠ 0) := by
  intro h
  have := certificate4664
  rw [h.1] at this
  norm_num at this
def C4665 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4665 : C4665.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4665 : ¬ (C4665.det = 0 ∧ ∀ i, C4665.adjugate i i ≠ 0) := by
  intro h
  have := certificate4665
  rw [h.1] at this
  norm_num at this
def C4666 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4666 : C4666.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4666 : ¬ (C4666.det = 0 ∧ ∀ i, C4666.adjugate i i ≠ 0) := by
  intro h
  have := certificate4666
  rw [h.1] at this
  norm_num at this
def C4667 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4667 : C4667.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4667 : ¬ (C4667.det = 0 ∧ ∀ i, C4667.adjugate i i ≠ 0) := by
  intro h
  have := certificate4667
  rw [h.1] at this
  norm_num at this
def C4668 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4668 : C4668.det = (25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4668 : ¬ (C4668.det = 0 ∧ ∀ i, C4668.adjugate i i ≠ 0) := by
  intro h
  have := certificate4668
  rw [h.1] at this
  norm_num at this
def C4669 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, -1, 0, -1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4669 : C4669.det = (-15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4669 : ¬ (C4669.det = 0 ∧ ∀ i, C4669.adjugate i i ≠ 0) := by
  intro h
  have := certificate4669
  rw [h.1] at this
  norm_num at this
def C4670 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4670 : C4670.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4670 : ¬ (C4670.det = 0 ∧ ∀ i, C4670.adjugate i i ≠ 0) := by
  intro h
  have := certificate4670
  rw [h.1] at this
  norm_num at this
def C4671 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4671 : C4671.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4671 : ¬ (C4671.det = 0 ∧ ∀ i, C4671.adjugate i i ≠ 0) := by
  intro h
  have := certificate4671
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0145
