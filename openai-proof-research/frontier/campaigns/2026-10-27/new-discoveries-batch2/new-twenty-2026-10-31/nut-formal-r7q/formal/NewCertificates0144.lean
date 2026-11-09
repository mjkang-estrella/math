import VerifiedDet
namespace Nut8.NewCertificates0144
def C4608 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4608 : C4608.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4608 : ¬ (C4608.det = 0 ∧ ∀ i, C4608.adjugate i i ≠ 0) := by
  intro h
  have := certificate4608
  rw [h.1] at this
  norm_num at this
def C4609 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4609 : C4609.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4609 : ¬ (C4609.det = 0 ∧ ∀ i, C4609.adjugate i i ≠ 0) := by
  intro h
  have := certificate4609
  rw [h.1] at this
  norm_num at this
def C4610 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4610 : C4610.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4610 : ¬ (C4610.det = 0 ∧ ∀ i, C4610.adjugate i i ≠ 0) := by
  intro h
  have := certificate4610
  rw [h.1] at this
  norm_num at this
def C4611 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4611 : C4611.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4611 : ¬ (C4611.det = 0 ∧ ∀ i, C4611.adjugate i i ≠ 0) := by
  intro h
  have := certificate4611
  rw [h.1] at this
  norm_num at this
def C4612 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4612 : C4612.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4612 : ¬ (C4612.det = 0 ∧ ∀ i, C4612.adjugate i i ≠ 0) := by
  intro h
  have := certificate4612
  rw [h.1] at this
  norm_num at this
def C4613 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4613 : C4613.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4613 : ¬ (C4613.det = 0 ∧ ∀ i, C4613.adjugate i i ≠ 0) := by
  intro h
  have := certificate4613
  rw [h.1] at this
  norm_num at this
def C4614 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4614 : C4614.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4614 : ¬ (C4614.det = 0 ∧ ∀ i, C4614.adjugate i i ≠ 0) := by
  intro h
  have := certificate4614
  rw [h.1] at this
  norm_num at this
def C4615 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4615 : C4615.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4615 : ¬ (C4615.det = 0 ∧ ∀ i, C4615.adjugate i i ≠ 0) := by
  intro h
  have := certificate4615
  rw [h.1] at this
  norm_num at this
def C4616 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4616 : C4616.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4616 : ¬ (C4616.det = 0 ∧ ∀ i, C4616.adjugate i i ≠ 0) := by
  intro h
  have := certificate4616
  rw [h.1] at this
  norm_num at this
def C4617 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4617 : C4617.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4617 : ¬ (C4617.det = 0 ∧ ∀ i, C4617.adjugate i i ≠ 0) := by
  intro h
  have := certificate4617
  rw [h.1] at this
  norm_num at this
def C4618 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4618 : C4618.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4618 : ¬ (C4618.det = 0 ∧ ∀ i, C4618.adjugate i i ≠ 0) := by
  intro h
  have := certificate4618
  rw [h.1] at this
  norm_num at this
def C4619 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4619 : C4619.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4619 : ¬ (C4619.det = 0 ∧ ∀ i, C4619.adjugate i i ≠ 0) := by
  intro h
  have := certificate4619
  rw [h.1] at this
  norm_num at this
def C4620 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4620 : C4620.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4620 : ¬ (C4620.det = 0 ∧ ∀ i, C4620.adjugate i i ≠ 0) := by
  intro h
  have := certificate4620
  rw [h.1] at this
  norm_num at this
def C4621 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate4621 : C4621.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4621 : ¬ (C4621.det = 0 ∧ ∀ i, C4621.adjugate i i ≠ 0) := by
  intro h
  have := certificate4621
  rw [h.1] at this
  norm_num at this
def C4622 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4622 : C4622.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4622 : ¬ (C4622.det = 0 ∧ ∀ i, C4622.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4622
def C4623 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4623 : C4623.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4623 : ¬ (C4623.det = 0 ∧ ∀ i, C4623.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4623
def C4624 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4624 : C4624.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4624 : ¬ (C4624.det = 0 ∧ ∀ i, C4624.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4624
def C4625 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4625 : C4625.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4625 : ¬ (C4625.det = 0 ∧ ∀ i, C4625.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate4625
def C4626 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4626 : C4626.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4626 : ¬ (C4626.det = 0 ∧ ∀ i, C4626.adjugate i i ≠ 0) := by
  intro h
  have := certificate4626
  rw [h.1] at this
  norm_num at this
def C4627 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4627 : C4627.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4627 : ¬ (C4627.det = 0 ∧ ∀ i, C4627.adjugate i i ≠ 0) := by
  intro h
  have := certificate4627
  rw [h.1] at this
  norm_num at this
def C4628 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4628 : C4628.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4628 : ¬ (C4628.det = 0 ∧ ∀ i, C4628.adjugate i i ≠ 0) := by
  intro h
  have := certificate4628
  rw [h.1] at this
  norm_num at this
def C4629 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, 1, -1, 0, 0; 0, 0, 1, 1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4629 : C4629.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4629 : ¬ (C4629.det = 0 ∧ ∀ i, C4629.adjugate i i ≠ 0) := by
  intro h
  have := certificate4629
  rw [h.1] at this
  norm_num at this
def C4630 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4630 : C4630.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4630 : ¬ (C4630.det = 0 ∧ ∀ i, C4630.adjugate i i ≠ 0) := by
  intro h
  have := certificate4630
  rw [h.1] at this
  norm_num at this
def C4631 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4631 : C4631.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4631 : ¬ (C4631.det = 0 ∧ ∀ i, C4631.adjugate i i ≠ 0) := by
  intro h
  have := certificate4631
  rw [h.1] at this
  norm_num at this
def C4632 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4632 : C4632.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4632 : ¬ (C4632.det = 0 ∧ ∀ i, C4632.adjugate i i ≠ 0) := by
  intro h
  have := certificate4632
  rw [h.1] at this
  norm_num at this
def C4633 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, 1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4633 : C4633.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4633 : ¬ (C4633.det = 0 ∧ ∀ i, C4633.adjugate i i ≠ 0) := by
  intro h
  have := certificate4633
  rw [h.1] at this
  norm_num at this
def C4634 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4634 : C4634.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4634 : ¬ (C4634.det = 0 ∧ ∀ i, C4634.adjugate i i ≠ 0) := by
  intro h
  have := certificate4634
  rw [h.1] at this
  norm_num at this
def C4635 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4635 : C4635.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4635 : ¬ (C4635.det = 0 ∧ ∀ i, C4635.adjugate i i ≠ 0) := by
  intro h
  have := certificate4635
  rw [h.1] at this
  norm_num at this
def C4636 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate4636 : C4636.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4636 : ¬ (C4636.det = 0 ∧ ∀ i, C4636.adjugate i i ≠ 0) := by
  intro h
  have := certificate4636
  rw [h.1] at this
  norm_num at this
def C4637 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 0, 0, -1, -1, 0, 0; 0, 0, 1, -1, -1, 0, 0, 0; 0, 0, 1, -1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate4637 : C4637.det = (-40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4637 : ¬ (C4637.det = 0 ∧ ∀ i, C4637.adjugate i i ≠ 0) := by
  intro h
  have := certificate4637
  rw [h.1] at this
  norm_num at this
def C4638 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4638 : C4638.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4638 : ¬ (C4638.det = 0 ∧ ∀ i, C4638.adjugate i i ≠ 0) := by
  intro h
  have := certificate4638
  rw [h.1] at this
  norm_num at this
def C4639 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate4639 : C4639.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4639 : ¬ (C4639.det = 0 ∧ ∀ i, C4639.adjugate i i ≠ 0) := by
  intro h
  have := certificate4639
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0144
