import VerifiedDet
namespace Nut8.NewCertificates0143
def C4576 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4576 : C4576.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4576 : ¬ (C4576.det = 0 ∧ ∀ i, C4576.adjugate i i ≠ 0) := by
  intro h
  have := certificate4576
  rw [h.1] at this
  norm_num at this
def C4577 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4577 : C4577.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4577 : ¬ (C4577.det = 0 ∧ ∀ i, C4577.adjugate i i ≠ 0) := by
  intro h
  have := certificate4577
  rw [h.1] at this
  norm_num at this
def C4578 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4578 : C4578.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4578 : ¬ (C4578.det = 0 ∧ ∀ i, C4578.adjugate i i ≠ 0) := by
  intro h
  have := certificate4578
  rw [h.1] at this
  norm_num at this
def C4579 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4579 : C4579.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4579 : ¬ (C4579.det = 0 ∧ ∀ i, C4579.adjugate i i ≠ 0) := by
  intro h
  have := certificate4579
  rw [h.1] at this
  norm_num at this
def C4580 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4580 : C4580.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4580 : ¬ (C4580.det = 0 ∧ ∀ i, C4580.adjugate i i ≠ 0) := by
  intro h
  have := certificate4580
  rw [h.1] at this
  norm_num at this
def C4581 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4581 : C4581.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4581 : ¬ (C4581.det = 0 ∧ ∀ i, C4581.adjugate i i ≠ 0) := by
  intro h
  have := certificate4581
  rw [h.1] at this
  norm_num at this
def C4582 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4582 : C4582.det = (-65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4582 : ¬ (C4582.det = 0 ∧ ∀ i, C4582.adjugate i i ≠ 0) := by
  intro h
  have := certificate4582
  rw [h.1] at this
  norm_num at this
def C4583 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4583 : C4583.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4583 : ¬ (C4583.det = 0 ∧ ∀ i, C4583.adjugate i i ≠ 0) := by
  intro h
  have := certificate4583
  rw [h.1] at this
  norm_num at this
def C4584 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4584 : C4584.det = (67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4584 : ¬ (C4584.det = 0 ∧ ∀ i, C4584.adjugate i i ≠ 0) := by
  intro h
  have := certificate4584
  rw [h.1] at this
  norm_num at this
def C4585 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4585 : C4585.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4585 : ¬ (C4585.det = 0 ∧ ∀ i, C4585.adjugate i i ≠ 0) := by
  intro h
  have := certificate4585
  rw [h.1] at this
  norm_num at this
def C4586 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4586 : C4586.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4586 : ¬ (C4586.det = 0 ∧ ∀ i, C4586.adjugate i i ≠ 0) := by
  intro h
  have := certificate4586
  rw [h.1] at this
  norm_num at this
def C4587 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4587 : C4587.det = (67 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4587 : ¬ (C4587.det = 0 ∧ ∀ i, C4587.adjugate i i ≠ 0) := by
  intro h
  have := certificate4587
  rw [h.1] at this
  norm_num at this
def C4588 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1]
theorem certificate4588 : C4588.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4588 : ¬ (C4588.det = 0 ∧ ∀ i, C4588.adjugate i i ≠ 0) := by
  intro h
  have := certificate4588
  rw [h.1] at this
  norm_num at this
def C4589 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, -1, 0, 0, -1, 0; 0, 0, 0, 1, 0, -1, -1, 0; 0, 0, 0, 0, 2, 0, 0, -1]
theorem certificate4589 : C4589.det = (-65 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4589 : ¬ (C4589.det = 0 ∧ ∀ i, C4589.adjugate i i ≠ 0) := by
  intro h
  have := certificate4589
  rw [h.1] at this
  norm_num at this
def C4590 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4590 : C4590.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4590 : ¬ (C4590.det = 0 ∧ ∀ i, C4590.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4590
def C4591 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4591 : C4591.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4591 : ¬ (C4591.det = 0 ∧ ∀ i, C4591.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4591
def C4592 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4592 : C4592.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4592 : ¬ (C4592.det = 0 ∧ ∀ i, C4592.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4592
def C4593 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4593 : C4593.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4593 : ¬ (C4593.det = 0 ∧ ∀ i, C4593.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4593
def C4594 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4594 : C4594.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4594 : ¬ (C4594.det = 0 ∧ ∀ i, C4594.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4594
def C4595 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4595 : C4595.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4595 : ¬ (C4595.det = 0 ∧ ∀ i, C4595.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4595
def C4596 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4596 : C4596.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4596 : ¬ (C4596.det = 0 ∧ ∀ i, C4596.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4596
def C4597 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4597 : C4597.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4597 : ¬ (C4597.det = 0 ∧ ∀ i, C4597.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4597
def C4598 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4598 : C4598.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4598 : ¬ (C4598.det = 0 ∧ ∀ i, C4598.adjugate i i ≠ 0) := by
  intro h
  have := certificate4598
  rw [h.1] at this
  norm_num at this
def C4599 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4599 : C4599.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4599 : ¬ (C4599.det = 0 ∧ ∀ i, C4599.adjugate i i ≠ 0) := by
  intro h
  have := certificate4599
  rw [h.1] at this
  norm_num at this
def C4600 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4600 : C4600.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4600 : ¬ (C4600.det = 0 ∧ ∀ i, C4600.adjugate i i ≠ 0) := by
  intro h
  have := certificate4600
  rw [h.1] at this
  norm_num at this
def C4601 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4601 : C4601.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4601 : ¬ (C4601.det = 0 ∧ ∀ i, C4601.adjugate i i ≠ 0) := by
  intro h
  have := certificate4601
  rw [h.1] at this
  norm_num at this
def C4602 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4602 : C4602.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4602 : ¬ (C4602.det = 0 ∧ ∀ i, C4602.adjugate i i ≠ 0) := by
  intro h
  have := certificate4602
  rw [h.1] at this
  norm_num at this
def C4603 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4603 : C4603.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4603 : ¬ (C4603.det = 0 ∧ ∀ i, C4603.adjugate i i ≠ 0) := by
  intro h
  have := certificate4603
  rw [h.1] at this
  norm_num at this
def C4604 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4604 : C4604.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4604 : ¬ (C4604.det = 0 ∧ ∀ i, C4604.adjugate i i ≠ 0) := by
  intro h
  have := certificate4604
  rw [h.1] at this
  norm_num at this
def C4605 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4605 : C4605.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4605 : ¬ (C4605.det = 0 ∧ ∀ i, C4605.adjugate i i ≠ 0) := by
  intro h
  have := certificate4605
  rw [h.1] at this
  norm_num at this
def C4606 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4606 : C4606.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4606 : ¬ (C4606.det = 0 ∧ ∀ i, C4606.adjugate i i ≠ 0) := by
  intro h
  have := certificate4606
  rw [h.1] at this
  norm_num at this
def C4607 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4607 : C4607.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4607 : ¬ (C4607.det = 0 ∧ ∀ i, C4607.adjugate i i ≠ 0) := by
  intro h
  have := certificate4607
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0143
