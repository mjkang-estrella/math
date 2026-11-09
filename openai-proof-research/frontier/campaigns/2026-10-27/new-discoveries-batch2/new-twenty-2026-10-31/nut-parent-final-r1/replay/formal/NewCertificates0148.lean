import VerifiedDet
namespace Nut8.NewCertificates0148
def C4736 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4736 : C4736.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4736 : ¬ (C4736.det = 0 ∧ ∀ i, C4736.adjugate i i ≠ 0) := by
  intro h
  have := certificate4736
  rw [h.1] at this
  norm_num at this
def C4737 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4737 : C4737.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4737 : ¬ (C4737.det = 0 ∧ ∀ i, C4737.adjugate i i ≠ 0) := by
  intro h
  have := certificate4737
  rw [h.1] at this
  norm_num at this
def C4738 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4738 : C4738.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4738 : ¬ (C4738.det = 0 ∧ ∀ i, C4738.adjugate i i ≠ 0) := by
  intro h
  have := certificate4738
  rw [h.1] at this
  norm_num at this
def C4739 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4739 : C4739.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4739 : ¬ (C4739.det = 0 ∧ ∀ i, C4739.adjugate i i ≠ 0) := by
  intro h
  have := certificate4739
  rw [h.1] at this
  norm_num at this
def C4740 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4740 : C4740.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4740 : ¬ (C4740.det = 0 ∧ ∀ i, C4740.adjugate i i ≠ 0) := by
  intro h
  have := certificate4740
  rw [h.1] at this
  norm_num at this
def C4741 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4741 : C4741.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4741 : ¬ (C4741.det = 0 ∧ ∀ i, C4741.adjugate i i ≠ 0) := by
  intro h
  have := certificate4741
  rw [h.1] at this
  norm_num at this
def C4742 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4742 : C4742.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4742 : ¬ (C4742.det = 0 ∧ ∀ i, C4742.adjugate i i ≠ 0) := by
  intro h
  have := certificate4742
  rw [h.1] at this
  norm_num at this
def C4743 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4743 : C4743.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4743 : ¬ (C4743.det = 0 ∧ ∀ i, C4743.adjugate i i ≠ 0) := by
  intro h
  have := certificate4743
  rw [h.1] at this
  norm_num at this
def C4744 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4744 : C4744.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4744 : ¬ (C4744.det = 0 ∧ ∀ i, C4744.adjugate i i ≠ 0) := by
  intro h
  have := certificate4744
  rw [h.1] at this
  norm_num at this
def C4745 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4745 : C4745.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4745 : ¬ (C4745.det = 0 ∧ ∀ i, C4745.adjugate i i ≠ 0) := by
  intro h
  have := certificate4745
  rw [h.1] at this
  norm_num at this
def C4746 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4746 : C4746.det = (10 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4746 : ¬ (C4746.det = 0 ∧ ∀ i, C4746.adjugate i i ≠ 0) := by
  intro h
  have := certificate4746
  rw [h.1] at this
  norm_num at this
def C4747 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4747 : C4747.det = (30 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4747 : ¬ (C4747.det = 0 ∧ ∀ i, C4747.adjugate i i ≠ 0) := by
  intro h
  have := certificate4747
  rw [h.1] at this
  norm_num at this
def C4748 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4748 : C4748.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4748 : ¬ (C4748.det = 0 ∧ ∀ i, C4748.adjugate i i ≠ 0) := by
  intro h
  have := certificate4748
  rw [h.1] at this
  norm_num at this
def C4749 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4749 : C4749.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4749 : ¬ (C4749.det = 0 ∧ ∀ i, C4749.adjugate i i ≠ 0) := by
  intro h
  have := certificate4749
  rw [h.1] at this
  norm_num at this
def C4750 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4750 : C4750.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4750 : ¬ (C4750.det = 0 ∧ ∀ i, C4750.adjugate i i ≠ 0) := by
  intro h
  have := certificate4750
  rw [h.1] at this
  norm_num at this
def C4751 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4751 : C4751.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4751 : ¬ (C4751.det = 0 ∧ ∀ i, C4751.adjugate i i ≠ 0) := by
  intro h
  have := certificate4751
  rw [h.1] at this
  norm_num at this
def C4752 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4752 : C4752.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4752 : ¬ (C4752.det = 0 ∧ ∀ i, C4752.adjugate i i ≠ 0) := by
  intro h
  have := certificate4752
  rw [h.1] at this
  norm_num at this
def C4753 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4753 : C4753.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4753 : ¬ (C4753.det = 0 ∧ ∀ i, C4753.adjugate i i ≠ 0) := by
  intro h
  have := certificate4753
  rw [h.1] at this
  norm_num at this
def C4754 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4754 : C4754.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4754 : ¬ (C4754.det = 0 ∧ ∀ i, C4754.adjugate i i ≠ 0) := by
  intro h
  have := certificate4754
  rw [h.1] at this
  norm_num at this
def C4755 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4755 : C4755.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4755 : ¬ (C4755.det = 0 ∧ ∀ i, C4755.adjugate i i ≠ 0) := by
  intro h
  have := certificate4755
  rw [h.1] at this
  norm_num at this
def C4756 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4756 : C4756.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4756 : ¬ (C4756.det = 0 ∧ ∀ i, C4756.adjugate i i ≠ 0) := by
  intro h
  have := certificate4756
  rw [h.1] at this
  norm_num at this
def C4757 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4757 : C4757.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4757 : ¬ (C4757.det = 0 ∧ ∀ i, C4757.adjugate i i ≠ 0) := by
  intro h
  have := certificate4757
  rw [h.1] at this
  norm_num at this
def C4758 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4758 : C4758.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4758 : ¬ (C4758.det = 0 ∧ ∀ i, C4758.adjugate i i ≠ 0) := by
  intro h
  have := certificate4758
  rw [h.1] at this
  norm_num at this
def C4759 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4759 : C4759.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4759 : ¬ (C4759.det = 0 ∧ ∀ i, C4759.adjugate i i ≠ 0) := by
  intro h
  have := certificate4759
  rw [h.1] at this
  norm_num at this
def C4760 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4760 : C4760.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4760 : ¬ (C4760.det = 0 ∧ ∀ i, C4760.adjugate i i ≠ 0) := by
  intro h
  have := certificate4760
  rw [h.1] at this
  norm_num at this
def C4761 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4761 : C4761.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4761 : ¬ (C4761.det = 0 ∧ ∀ i, C4761.adjugate i i ≠ 0) := by
  intro h
  have := certificate4761
  rw [h.1] at this
  norm_num at this
def C4762 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4762 : C4762.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4762 : ¬ (C4762.det = 0 ∧ ∀ i, C4762.adjugate i i ≠ 0) := by
  intro h
  have := certificate4762
  rw [h.1] at this
  norm_num at this
def C4763 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4763 : C4763.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4763 : ¬ (C4763.det = 0 ∧ ∀ i, C4763.adjugate i i ≠ 0) := by
  intro h
  have := certificate4763
  rw [h.1] at this
  norm_num at this
def C4764 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4764 : C4764.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4764 : ¬ (C4764.det = 0 ∧ ∀ i, C4764.adjugate i i ≠ 0) := by
  intro h
  have := certificate4764
  rw [h.1] at this
  norm_num at this
def C4765 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4765 : C4765.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4765 : ¬ (C4765.det = 0 ∧ ∀ i, C4765.adjugate i i ≠ 0) := by
  intro h
  have := certificate4765
  rw [h.1] at this
  norm_num at this
def C4766 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4766 : C4766.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4766 : ¬ (C4766.det = 0 ∧ ∀ i, C4766.adjugate i i ≠ 0) := by
  intro h
  have := certificate4766
  rw [h.1] at this
  norm_num at this
def C4767 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4767 : C4767.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4767 : ¬ (C4767.det = 0 ∧ ∀ i, C4767.adjugate i i ≠ 0) := by
  intro h
  have := certificate4767
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0148
