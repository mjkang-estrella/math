import VerifiedDet
namespace Nut8.NewCertificates0020
def C640 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate640 : C640.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction640 : ¬ (C640.det = 0 ∧ ∀ i, C640.adjugate i i ≠ 0) := by
  intro h
  have := certificate640
  rw [h.1] at this
  norm_num at this
def C641 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate641 : C641.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction641 : ¬ (C641.det = 0 ∧ ∀ i, C641.adjugate i i ≠ 0) := by
  intro h
  have := certificate641
  rw [h.1] at this
  norm_num at this
def C642 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate642 : C642.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction642 : ¬ (C642.det = 0 ∧ ∀ i, C642.adjugate i i ≠ 0) := by
  intro h
  have := certificate642
  rw [h.1] at this
  norm_num at this
def C643 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate643 : C643.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction643 : ¬ (C643.det = 0 ∧ ∀ i, C643.adjugate i i ≠ 0) := by
  intro h
  have := certificate643
  rw [h.1] at this
  norm_num at this
def C644 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate644 : C644.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction644 : ¬ (C644.det = 0 ∧ ∀ i, C644.adjugate i i ≠ 0) := by
  intro h
  have := certificate644
  rw [h.1] at this
  norm_num at this
def C645 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate645 : C645.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction645 : ¬ (C645.det = 0 ∧ ∀ i, C645.adjugate i i ≠ 0) := by
  intro h
  have := certificate645
  rw [h.1] at this
  norm_num at this
def C646 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate646 : C646.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction646 : ¬ (C646.det = 0 ∧ ∀ i, C646.adjugate i i ≠ 0) := by
  intro h
  have := certificate646
  rw [h.1] at this
  norm_num at this
def C647 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate647 : C647.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction647 : ¬ (C647.det = 0 ∧ ∀ i, C647.adjugate i i ≠ 0) := by
  intro h
  have := certificate647
  rw [h.1] at this
  norm_num at this
def C648 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate648 : C648.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction648 : ¬ (C648.det = 0 ∧ ∀ i, C648.adjugate i i ≠ 0) := by
  intro h
  have := certificate648
  rw [h.1] at this
  norm_num at this
def C649 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate649 : C649.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction649 : ¬ (C649.det = 0 ∧ ∀ i, C649.adjugate i i ≠ 0) := by
  intro h
  have := certificate649
  rw [h.1] at this
  norm_num at this
def C650 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate650 : C650.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction650 : ¬ (C650.det = 0 ∧ ∀ i, C650.adjugate i i ≠ 0) := by
  intro h
  have := certificate650
  rw [h.1] at this
  norm_num at this
def C651 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate651 : C651.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction651 : ¬ (C651.det = 0 ∧ ∀ i, C651.adjugate i i ≠ 0) := by
  intro h
  have := certificate651
  rw [h.1] at this
  norm_num at this
def C652 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate652 : C652.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction652 : ¬ (C652.det = 0 ∧ ∀ i, C652.adjugate i i ≠ 0) := by
  intro h
  have := certificate652
  rw [h.1] at this
  norm_num at this
def C653 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate653 : C653.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction653 : ¬ (C653.det = 0 ∧ ∀ i, C653.adjugate i i ≠ 0) := by
  intro h
  have := certificate653
  rw [h.1] at this
  norm_num at this
def C654 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate654 : C654.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction654 : ¬ (C654.det = 0 ∧ ∀ i, C654.adjugate i i ≠ 0) := by
  intro h
  have := certificate654
  rw [h.1] at this
  norm_num at this
def C655 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate655 : C655.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction655 : ¬ (C655.det = 0 ∧ ∀ i, C655.adjugate i i ≠ 0) := by
  intro h
  have := certificate655
  rw [h.1] at this
  norm_num at this
def C656 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate656 : C656.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction656 : ¬ (C656.det = 0 ∧ ∀ i, C656.adjugate i i ≠ 0) := by
  intro h
  have := certificate656
  rw [h.1] at this
  norm_num at this
def C657 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate657 : C657.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction657 : ¬ (C657.det = 0 ∧ ∀ i, C657.adjugate i i ≠ 0) := by
  intro h
  have := certificate657
  rw [h.1] at this
  norm_num at this
def C658 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate658 : C658.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction658 : ¬ (C658.det = 0 ∧ ∀ i, C658.adjugate i i ≠ 0) := by
  intro h
  have := certificate658
  rw [h.1] at this
  norm_num at this
def C659 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate659 : C659.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction659 : ¬ (C659.det = 0 ∧ ∀ i, C659.adjugate i i ≠ 0) := by
  intro h
  have := certificate659
  rw [h.1] at this
  norm_num at this
def C660 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate660 : C660.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction660 : ¬ (C660.det = 0 ∧ ∀ i, C660.adjugate i i ≠ 0) := by
  intro h
  have := certificate660
  rw [h.1] at this
  norm_num at this
def C661 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate661 : C661.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction661 : ¬ (C661.det = 0 ∧ ∀ i, C661.adjugate i i ≠ 0) := by
  intro h
  have := certificate661
  rw [h.1] at this
  norm_num at this
def C662 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate662 : C662.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction662 : ¬ (C662.det = 0 ∧ ∀ i, C662.adjugate i i ≠ 0) := by
  intro h
  have := certificate662
  rw [h.1] at this
  norm_num at this
def C663 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, -1, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate663 : C663.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction663 : ¬ (C663.det = 0 ∧ ∀ i, C663.adjugate i i ≠ 0) := by
  intro h
  have := certificate663
  rw [h.1] at this
  norm_num at this
def C664 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate664 : C664.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction664 : ¬ (C664.det = 0 ∧ ∀ i, C664.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate664
def C665 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate665 : C665.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction665 : ¬ (C665.det = 0 ∧ ∀ i, C665.adjugate i i ≠ 0) := by
  intro h
  have := certificate665
  rw [h.1] at this
  norm_num at this
def C666 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate666 : C666.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction666 : ¬ (C666.det = 0 ∧ ∀ i, C666.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate666
def C667 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate667 : C667.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction667 : ¬ (C667.det = 0 ∧ ∀ i, C667.adjugate i i ≠ 0) := by
  intro h
  have := certificate667
  rw [h.1] at this
  norm_num at this
def C668 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate668 : C668.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction668 : ¬ (C668.det = 0 ∧ ∀ i, C668.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate668
def C669 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate669 : C669.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction669 : ¬ (C669.det = 0 ∧ ∀ i, C669.adjugate i i ≠ 0) := by
  intro h
  have := certificate669
  rw [h.1] at this
  norm_num at this
def C670 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate670 : C670.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction670 : ¬ (C670.det = 0 ∧ ∀ i, C670.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate670
def C671 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate671 : C671.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction671 : ¬ (C671.det = 0 ∧ ∀ i, C671.adjugate i i ≠ 0) := by
  intro h
  have := certificate671
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0020
