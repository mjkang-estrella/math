import VerifiedDet
namespace Nut8.NewCertificates0238
def C7616 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7616 : C7616.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7616 : ¬ (C7616.det = 0 ∧ ∀ i, C7616.adjugate i i ≠ 0) := by
  intro h
  have := certificate7616
  rw [h.1] at this
  norm_num at this
def C7617 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate7617 : C7617.det = (6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7617 : ¬ (C7617.det = 0 ∧ ∀ i, C7617.adjugate i i ≠ 0) := by
  intro h
  have := certificate7617
  rw [h.1] at this
  norm_num at this
def C7618 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7618 : C7618.det = (42 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7618 : ¬ (C7618.det = 0 ∧ ∀ i, C7618.adjugate i i ≠ 0) := by
  intro h
  have := certificate7618
  rw [h.1] at this
  norm_num at this
def C7619 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, -1, 1, 0, 0, 0, 0; 1, -1, 0, -1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate7619 : C7619.det = (22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7619 : ¬ (C7619.det = 0 ∧ ∀ i, C7619.adjugate i i ≠ 0) := by
  intro h
  have := certificate7619
  rw [h.1] at this
  norm_num at this
def C7620 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7620 : C7620.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7620 : ¬ (C7620.det = 0 ∧ ∀ i, C7620.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7620
def C7621 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7621 : C7621.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7621 : ¬ (C7621.det = 0 ∧ ∀ i, C7621.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7621
def C7622 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7622 : C7622.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7622 : ¬ (C7622.det = 0 ∧ ∀ i, C7622.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7622
def C7623 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7623 : C7623.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7623 : ¬ (C7623.det = 0 ∧ ∀ i, C7623.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7623
def C7624 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7624 : C7624.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7624 : ¬ (C7624.det = 0 ∧ ∀ i, C7624.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7624
def C7625 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7625 : C7625.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7625 : ¬ (C7625.det = 0 ∧ ∀ i, C7625.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7625
def C7626 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7626 : C7626.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7626 : ¬ (C7626.det = 0 ∧ ∀ i, C7626.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7626
def C7627 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7627 : C7627.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7627 : ¬ (C7627.det = 0 ∧ ∀ i, C7627.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7627
def C7628 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7628 : C7628.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7628 : ¬ (C7628.det = 0 ∧ ∀ i, C7628.adjugate i i ≠ 0) := by
  intro h
  have := certificate7628
  rw [h.1] at this
  norm_num at this
def C7629 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7629 : C7629.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7629 : ¬ (C7629.det = 0 ∧ ∀ i, C7629.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate7629
def C7630 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7630 : C7630.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7630 : ¬ (C7630.det = 0 ∧ ∀ i, C7630.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate7630
def C7631 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7631 : C7631.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7631 : ¬ (C7631.det = 0 ∧ ∀ i, C7631.adjugate i i ≠ 0) := by
  intro h
  have := certificate7631
  rw [h.1] at this
  norm_num at this
def C7632 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7632 : C7632.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7632 : ¬ (C7632.det = 0 ∧ ∀ i, C7632.adjugate i i ≠ 0) := by
  intro h
  have := certificate7632
  rw [h.1] at this
  norm_num at this
def C7633 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7633 : C7633.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7633 : ¬ (C7633.det = 0 ∧ ∀ i, C7633.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate7633
def C7634 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7634 : C7634.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7634 : ¬ (C7634.det = 0 ∧ ∀ i, C7634.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate7634
def C7635 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7635 : C7635.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7635 : ¬ (C7635.det = 0 ∧ ∀ i, C7635.adjugate i i ≠ 0) := by
  intro h
  have := certificate7635
  rw [h.1] at this
  norm_num at this
def C7636 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7636 : C7636.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7636 : ¬ (C7636.det = 0 ∧ ∀ i, C7636.adjugate i i ≠ 0) := by
  intro h
  have := certificate7636
  rw [h.1] at this
  norm_num at this
def C7637 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7637 : C7637.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7637 : ¬ (C7637.det = 0 ∧ ∀ i, C7637.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7637
def C7638 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7638 : C7638.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7638 : ¬ (C7638.det = 0 ∧ ∀ i, C7638.adjugate i i ≠ 0) := by
  intro h
  have := certificate7638
  rw [h.1] at this
  norm_num at this
def C7639 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7639 : C7639.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7639 : ¬ (C7639.det = 0 ∧ ∀ i, C7639.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7639
def C7640 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7640 : C7640.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7640 : ¬ (C7640.det = 0 ∧ ∀ i, C7640.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7640
def C7641 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7641 : C7641.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7641 : ¬ (C7641.det = 0 ∧ ∀ i, C7641.adjugate i i ≠ 0) := by
  intro h
  have := certificate7641
  rw [h.1] at this
  norm_num at this
def C7642 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7642 : C7642.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7642 : ¬ (C7642.det = 0 ∧ ∀ i, C7642.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate7642
def C7643 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7643 : C7643.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7643 : ¬ (C7643.det = 0 ∧ ∀ i, C7643.adjugate i i ≠ 0) := by
  intro h
  have := certificate7643
  rw [h.1] at this
  norm_num at this
def C7644 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0]
theorem certificate7644 : C7644.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7644 : ¬ (C7644.det = 0 ∧ ∀ i, C7644.adjugate i i ≠ 0) := by
  intro h
  have := certificate7644
  rw [h.1] at this
  norm_num at this
def C7645 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, 1, -1, 0]
theorem certificate7645 : C7645.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7645 : ¬ (C7645.det = 0 ∧ ∀ i, C7645.adjugate i i ≠ 0) := by
  intro h
  have := certificate7645
  rw [h.1] at this
  norm_num at this
def C7646 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, -1, 1, 0]
theorem certificate7646 : C7646.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7646 : ¬ (C7646.det = 0 ∧ ∀ i, C7646.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7646
def C7647 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, -1, 0, 1, 0; 1, 0, 0, 0, -1, 0, 0, 1; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 0, 1, 0, -1, -1, 0]
theorem certificate7647 : C7647.adjugate 1 1 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7647 : ¬ (C7647.det = 0 ∧ ∀ i, C7647.adjugate i i ≠ 0) := by
  intro h
  exact h.2 1 certificate7647
end Nut8.NewCertificates0238
