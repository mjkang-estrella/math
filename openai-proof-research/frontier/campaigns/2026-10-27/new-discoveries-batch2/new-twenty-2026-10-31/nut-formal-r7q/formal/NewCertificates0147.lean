import VerifiedDet
namespace Nut8.NewCertificates0147
def C4704 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4704 : C4704.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4704 : ¬ (C4704.det = 0 ∧ ∀ i, C4704.adjugate i i ≠ 0) := by
  intro h
  have := certificate4704
  rw [h.1] at this
  norm_num at this
def C4705 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4705 : C4705.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4705 : ¬ (C4705.det = 0 ∧ ∀ i, C4705.adjugate i i ≠ 0) := by
  intro h
  have := certificate4705
  rw [h.1] at this
  norm_num at this
def C4706 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4706 : C4706.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4706 : ¬ (C4706.det = 0 ∧ ∀ i, C4706.adjugate i i ≠ 0) := by
  intro h
  have := certificate4706
  rw [h.1] at this
  norm_num at this
def C4707 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4707 : C4707.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4707 : ¬ (C4707.det = 0 ∧ ∀ i, C4707.adjugate i i ≠ 0) := by
  intro h
  have := certificate4707
  rw [h.1] at this
  norm_num at this
def C4708 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4708 : C4708.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4708 : ¬ (C4708.det = 0 ∧ ∀ i, C4708.adjugate i i ≠ 0) := by
  intro h
  have := certificate4708
  rw [h.1] at this
  norm_num at this
def C4709 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4709 : C4709.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4709 : ¬ (C4709.det = 0 ∧ ∀ i, C4709.adjugate i i ≠ 0) := by
  intro h
  have := certificate4709
  rw [h.1] at this
  norm_num at this
def C4710 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4710 : C4710.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4710 : ¬ (C4710.det = 0 ∧ ∀ i, C4710.adjugate i i ≠ 0) := by
  intro h
  have := certificate4710
  rw [h.1] at this
  norm_num at this
def C4711 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4711 : C4711.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4711 : ¬ (C4711.det = 0 ∧ ∀ i, C4711.adjugate i i ≠ 0) := by
  intro h
  have := certificate4711
  rw [h.1] at this
  norm_num at this
def C4712 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4712 : C4712.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4712 : ¬ (C4712.det = 0 ∧ ∀ i, C4712.adjugate i i ≠ 0) := by
  intro h
  have := certificate4712
  rw [h.1] at this
  norm_num at this
def C4713 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4713 : C4713.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4713 : ¬ (C4713.det = 0 ∧ ∀ i, C4713.adjugate i i ≠ 0) := by
  intro h
  have := certificate4713
  rw [h.1] at this
  norm_num at this
def C4714 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4714 : C4714.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4714 : ¬ (C4714.det = 0 ∧ ∀ i, C4714.adjugate i i ≠ 0) := by
  intro h
  have := certificate4714
  rw [h.1] at this
  norm_num at this
def C4715 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4715 : C4715.det = (11 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4715 : ¬ (C4715.det = 0 ∧ ∀ i, C4715.adjugate i i ≠ 0) := by
  intro h
  have := certificate4715
  rw [h.1] at this
  norm_num at this
def C4716 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate4716 : C4716.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4716 : ¬ (C4716.det = 0 ∧ ∀ i, C4716.adjugate i i ≠ 0) := by
  intro h
  have := certificate4716
  rw [h.1] at this
  norm_num at this
def C4717 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate4717 : C4717.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4717 : ¬ (C4717.det = 0 ∧ ∀ i, C4717.adjugate i i ≠ 0) := by
  intro h
  have := certificate4717
  rw [h.1] at this
  norm_num at this
def C4718 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4718 : C4718.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4718 : ¬ (C4718.det = 0 ∧ ∀ i, C4718.adjugate i i ≠ 0) := by
  intro h
  have := certificate4718
  rw [h.1] at this
  norm_num at this
def C4719 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4719 : C4719.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4719 : ¬ (C4719.det = 0 ∧ ∀ i, C4719.adjugate i i ≠ 0) := by
  intro h
  have := certificate4719
  rw [h.1] at this
  norm_num at this
def C4720 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4720 : C4720.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4720 : ¬ (C4720.det = 0 ∧ ∀ i, C4720.adjugate i i ≠ 0) := by
  intro h
  have := certificate4720
  rw [h.1] at this
  norm_num at this
def C4721 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4721 : C4721.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4721 : ¬ (C4721.det = 0 ∧ ∀ i, C4721.adjugate i i ≠ 0) := by
  intro h
  have := certificate4721
  rw [h.1] at this
  norm_num at this
def C4722 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4722 : C4722.det = (-50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4722 : ¬ (C4722.det = 0 ∧ ∀ i, C4722.adjugate i i ≠ 0) := by
  intro h
  have := certificate4722
  rw [h.1] at this
  norm_num at this
def C4723 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4723 : C4723.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4723 : ¬ (C4723.det = 0 ∧ ∀ i, C4723.adjugate i i ≠ 0) := by
  intro h
  have := certificate4723
  rw [h.1] at this
  norm_num at this
def C4724 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4724 : C4724.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4724 : ¬ (C4724.det = 0 ∧ ∀ i, C4724.adjugate i i ≠ 0) := by
  intro h
  have := certificate4724
  rw [h.1] at this
  norm_num at this
def C4725 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4725 : C4725.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4725 : ¬ (C4725.det = 0 ∧ ∀ i, C4725.adjugate i i ≠ 0) := by
  intro h
  have := certificate4725
  rw [h.1] at this
  norm_num at this
def C4726 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4726 : C4726.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4726 : ¬ (C4726.det = 0 ∧ ∀ i, C4726.adjugate i i ≠ 0) := by
  intro h
  have := certificate4726
  rw [h.1] at this
  norm_num at this
def C4727 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4727 : C4727.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4727 : ¬ (C4727.det = 0 ∧ ∀ i, C4727.adjugate i i ≠ 0) := by
  intro h
  have := certificate4727
  rw [h.1] at this
  norm_num at this
def C4728 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4728 : C4728.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4728 : ¬ (C4728.det = 0 ∧ ∀ i, C4728.adjugate i i ≠ 0) := by
  intro h
  have := certificate4728
  rw [h.1] at this
  norm_num at this
def C4729 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate4729 : C4729.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4729 : ¬ (C4729.det = 0 ∧ ∀ i, C4729.adjugate i i ≠ 0) := by
  intro h
  have := certificate4729
  rw [h.1] at this
  norm_num at this
def C4730 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4730 : C4730.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4730 : ¬ (C4730.det = 0 ∧ ∀ i, C4730.adjugate i i ≠ 0) := by
  intro h
  have := certificate4730
  rw [h.1] at this
  norm_num at this
def C4731 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4731 : C4731.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4731 : ¬ (C4731.det = 0 ∧ ∀ i, C4731.adjugate i i ≠ 0) := by
  intro h
  have := certificate4731
  rw [h.1] at this
  norm_num at this
def C4732 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4732 : C4732.det = (2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4732 : ¬ (C4732.det = 0 ∧ ∀ i, C4732.adjugate i i ≠ 0) := by
  intro h
  have := certificate4732
  rw [h.1] at this
  norm_num at this
def C4733 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate4733 : C4733.det = (-50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4733 : ¬ (C4733.det = 0 ∧ ∀ i, C4733.adjugate i i ≠ 0) := by
  intro h
  have := certificate4733
  rw [h.1] at this
  norm_num at this
def C4734 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate4734 : C4734.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4734 : ¬ (C4734.det = 0 ∧ ∀ i, C4734.adjugate i i ≠ 0) := by
  intro h
  have := certificate4734
  rw [h.1] at this
  norm_num at this
def C4735 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate4735 : C4735.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4735 : ¬ (C4735.det = 0 ∧ ∀ i, C4735.adjugate i i ≠ 0) := by
  intro h
  have := certificate4735
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0147
