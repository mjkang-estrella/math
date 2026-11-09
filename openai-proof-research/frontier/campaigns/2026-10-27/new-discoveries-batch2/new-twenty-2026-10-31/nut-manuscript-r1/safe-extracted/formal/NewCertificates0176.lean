import VerifiedDet
namespace Nut8.NewCertificates0176
def C5632 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5632 : C5632.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5632 : ¬ (C5632.det = 0 ∧ ∀ i, C5632.adjugate i i ≠ 0) := by
  intro h
  have := certificate5632
  rw [h.1] at this
  norm_num at this
def C5633 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5633 : C5633.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5633 : ¬ (C5633.det = 0 ∧ ∀ i, C5633.adjugate i i ≠ 0) := by
  intro h
  have := certificate5633
  rw [h.1] at this
  norm_num at this
def C5634 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5634 : C5634.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5634 : ¬ (C5634.det = 0 ∧ ∀ i, C5634.adjugate i i ≠ 0) := by
  intro h
  have := certificate5634
  rw [h.1] at this
  norm_num at this
def C5635 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, -1, 0, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5635 : C5635.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5635 : ¬ (C5635.det = 0 ∧ ∀ i, C5635.adjugate i i ≠ 0) := by
  intro h
  have := certificate5635
  rw [h.1] at this
  norm_num at this
def C5636 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5636 : C5636.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5636 : ¬ (C5636.det = 0 ∧ ∀ i, C5636.adjugate i i ≠ 0) := by
  intro h
  have := certificate5636
  rw [h.1] at this
  norm_num at this
def C5637 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5637 : C5637.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5637 : ¬ (C5637.det = 0 ∧ ∀ i, C5637.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate5637
def C5638 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5638 : C5638.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5638 : ¬ (C5638.det = 0 ∧ ∀ i, C5638.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate5638
def C5639 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5639 : C5639.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5639 : ¬ (C5639.det = 0 ∧ ∀ i, C5639.adjugate i i ≠ 0) := by
  intro h
  have := certificate5639
  rw [h.1] at this
  norm_num at this
def C5640 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5640 : C5640.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5640 : ¬ (C5640.det = 0 ∧ ∀ i, C5640.adjugate i i ≠ 0) := by
  intro h
  have := certificate5640
  rw [h.1] at this
  norm_num at this
def C5641 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5641 : C5641.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5641 : ¬ (C5641.det = 0 ∧ ∀ i, C5641.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5641
def C5642 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5642 : C5642.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5642 : ¬ (C5642.det = 0 ∧ ∀ i, C5642.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5642
def C5643 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, -1, 0, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, -1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5643 : C5643.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5643 : ¬ (C5643.det = 0 ∧ ∀ i, C5643.adjugate i i ≠ 0) := by
  intro h
  have := certificate5643
  rw [h.1] at this
  norm_num at this
def C5644 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5644 : C5644.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5644 : ¬ (C5644.det = 0 ∧ ∀ i, C5644.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5644
def C5645 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5645 : C5645.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5645 : ¬ (C5645.det = 0 ∧ ∀ i, C5645.adjugate i i ≠ 0) := by
  intro h
  have := certificate5645
  rw [h.1] at this
  norm_num at this
def C5646 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5646 : C5646.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5646 : ¬ (C5646.det = 0 ∧ ∀ i, C5646.adjugate i i ≠ 0) := by
  intro h
  have := certificate5646
  rw [h.1] at this
  norm_num at this
def C5647 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5647 : C5647.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5647 : ¬ (C5647.det = 0 ∧ ∀ i, C5647.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5647
def C5648 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5648 : C5648.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5648 : ¬ (C5648.det = 0 ∧ ∀ i, C5648.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5648
def C5649 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5649 : C5649.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5649 : ¬ (C5649.det = 0 ∧ ∀ i, C5649.adjugate i i ≠ 0) := by
  intro h
  have := certificate5649
  rw [h.1] at this
  norm_num at this
def C5650 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5650 : C5650.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5650 : ¬ (C5650.det = 0 ∧ ∀ i, C5650.adjugate i i ≠ 0) := by
  intro h
  have := certificate5650
  rw [h.1] at this
  norm_num at this
def C5651 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5651 : C5651.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5651 : ¬ (C5651.det = 0 ∧ ∀ i, C5651.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5651
def C5652 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5652 : C5652.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5652 : ¬ (C5652.det = 0 ∧ ∀ i, C5652.adjugate i i ≠ 0) := by
  intro h
  have := certificate5652
  rw [h.1] at this
  norm_num at this
def C5653 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5653 : C5653.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5653 : ¬ (C5653.det = 0 ∧ ∀ i, C5653.adjugate i i ≠ 0) := by
  intro h
  have := certificate5653
  rw [h.1] at this
  norm_num at this
def C5654 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5654 : C5654.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5654 : ¬ (C5654.det = 0 ∧ ∀ i, C5654.adjugate i i ≠ 0) := by
  intro h
  have := certificate5654
  rw [h.1] at this
  norm_num at this
def C5655 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5655 : C5655.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5655 : ¬ (C5655.det = 0 ∧ ∀ i, C5655.adjugate i i ≠ 0) := by
  intro h
  have := certificate5655
  rw [h.1] at this
  norm_num at this
def C5656 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5656 : C5656.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5656 : ¬ (C5656.det = 0 ∧ ∀ i, C5656.adjugate i i ≠ 0) := by
  intro h
  have := certificate5656
  rw [h.1] at this
  norm_num at this
def C5657 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5657 : C5657.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5657 : ¬ (C5657.det = 0 ∧ ∀ i, C5657.adjugate i i ≠ 0) := by
  intro h
  have := certificate5657
  rw [h.1] at this
  norm_num at this
def C5658 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5658 : C5658.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5658 : ¬ (C5658.det = 0 ∧ ∀ i, C5658.adjugate i i ≠ 0) := by
  intro h
  have := certificate5658
  rw [h.1] at this
  norm_num at this
def C5659 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5659 : C5659.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5659 : ¬ (C5659.det = 0 ∧ ∀ i, C5659.adjugate i i ≠ 0) := by
  intro h
  have := certificate5659
  rw [h.1] at this
  norm_num at this
def C5660 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5660 : C5660.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5660 : ¬ (C5660.det = 0 ∧ ∀ i, C5660.adjugate i i ≠ 0) := by
  intro h
  have := certificate5660
  rw [h.1] at this
  norm_num at this
def C5661 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5661 : C5661.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5661 : ¬ (C5661.det = 0 ∧ ∀ i, C5661.adjugate i i ≠ 0) := by
  intro h
  have := certificate5661
  rw [h.1] at this
  norm_num at this
def C5662 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5662 : C5662.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5662 : ¬ (C5662.det = 0 ∧ ∀ i, C5662.adjugate i i ≠ 0) := by
  intro h
  have := certificate5662
  rw [h.1] at this
  norm_num at this
def C5663 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5663 : C5663.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5663 : ¬ (C5663.det = 0 ∧ ∀ i, C5663.adjugate i i ≠ 0) := by
  intro h
  have := certificate5663
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0176
