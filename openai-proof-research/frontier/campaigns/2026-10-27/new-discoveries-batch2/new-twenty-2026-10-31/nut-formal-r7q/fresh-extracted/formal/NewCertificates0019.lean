import VerifiedDet
namespace Nut8.NewCertificates0019
def C608 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate608 : C608.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction608 : ¬ (C608.det = 0 ∧ ∀ i, C608.adjugate i i ≠ 0) := by
  intro h
  have := certificate608
  rw [h.1] at this
  norm_num at this
def C609 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate609 : C609.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction609 : ¬ (C609.det = 0 ∧ ∀ i, C609.adjugate i i ≠ 0) := by
  intro h
  have := certificate609
  rw [h.1] at this
  norm_num at this
def C610 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate610 : C610.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction610 : ¬ (C610.det = 0 ∧ ∀ i, C610.adjugate i i ≠ 0) := by
  intro h
  have := certificate610
  rw [h.1] at this
  norm_num at this
def C611 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate611 : C611.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction611 : ¬ (C611.det = 0 ∧ ∀ i, C611.adjugate i i ≠ 0) := by
  intro h
  have := certificate611
  rw [h.1] at this
  norm_num at this
def C612 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate612 : C612.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction612 : ¬ (C612.det = 0 ∧ ∀ i, C612.adjugate i i ≠ 0) := by
  intro h
  have := certificate612
  rw [h.1] at this
  norm_num at this
def C613 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate613 : C613.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction613 : ¬ (C613.det = 0 ∧ ∀ i, C613.adjugate i i ≠ 0) := by
  intro h
  have := certificate613
  rw [h.1] at this
  norm_num at this
def C614 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate614 : C614.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction614 : ¬ (C614.det = 0 ∧ ∀ i, C614.adjugate i i ≠ 0) := by
  intro h
  have := certificate614
  rw [h.1] at this
  norm_num at this
def C615 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate615 : C615.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction615 : ¬ (C615.det = 0 ∧ ∀ i, C615.adjugate i i ≠ 0) := by
  intro h
  have := certificate615
  rw [h.1] at this
  norm_num at this
def C616 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate616 : C616.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction616 : ¬ (C616.det = 0 ∧ ∀ i, C616.adjugate i i ≠ 0) := by
  intro h
  have := certificate616
  rw [h.1] at this
  norm_num at this
def C617 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate617 : C617.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction617 : ¬ (C617.det = 0 ∧ ∀ i, C617.adjugate i i ≠ 0) := by
  intro h
  have := certificate617
  rw [h.1] at this
  norm_num at this
def C618 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate618 : C618.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction618 : ¬ (C618.det = 0 ∧ ∀ i, C618.adjugate i i ≠ 0) := by
  intro h
  have := certificate618
  rw [h.1] at this
  norm_num at this
def C619 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate619 : C619.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction619 : ¬ (C619.det = 0 ∧ ∀ i, C619.adjugate i i ≠ 0) := by
  intro h
  have := certificate619
  rw [h.1] at this
  norm_num at this
def C620 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate620 : C620.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction620 : ¬ (C620.det = 0 ∧ ∀ i, C620.adjugate i i ≠ 0) := by
  intro h
  have := certificate620
  rw [h.1] at this
  norm_num at this
def C621 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, 2]
theorem certificate621 : C621.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction621 : ¬ (C621.det = 0 ∧ ∀ i, C621.adjugate i i ≠ 0) := by
  intro h
  have := certificate621
  rw [h.1] at this
  norm_num at this
def C622 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate622 : C622.det = (-84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction622 : ¬ (C622.det = 0 ∧ ∀ i, C622.adjugate i i ≠ 0) := by
  intro h
  have := certificate622
  rw [h.1] at this
  norm_num at this
def C623 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 1, 0, -2]
theorem certificate623 : C623.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction623 : ¬ (C623.det = 0 ∧ ∀ i, C623.adjugate i i ≠ 0) := by
  intro h
  have := certificate623
  rw [h.1] at this
  norm_num at this
def C624 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate624 : C624.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction624 : ¬ (C624.det = 0 ∧ ∀ i, C624.adjugate i i ≠ 0) := by
  intro h
  have := certificate624
  rw [h.1] at this
  norm_num at this
def C625 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate625 : C625.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction625 : ¬ (C625.det = 0 ∧ ∀ i, C625.adjugate i i ≠ 0) := by
  intro h
  have := certificate625
  rw [h.1] at this
  norm_num at this
def C626 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate626 : C626.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction626 : ¬ (C626.det = 0 ∧ ∀ i, C626.adjugate i i ≠ 0) := by
  intro h
  have := certificate626
  rw [h.1] at this
  norm_num at this
def C627 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate627 : C627.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction627 : ¬ (C627.det = 0 ∧ ∀ i, C627.adjugate i i ≠ 0) := by
  intro h
  have := certificate627
  rw [h.1] at this
  norm_num at this
def C628 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate628 : C628.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction628 : ¬ (C628.det = 0 ∧ ∀ i, C628.adjugate i i ≠ 0) := by
  intro h
  have := certificate628
  rw [h.1] at this
  norm_num at this
def C629 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate629 : C629.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction629 : ¬ (C629.det = 0 ∧ ∀ i, C629.adjugate i i ≠ 0) := by
  intro h
  have := certificate629
  rw [h.1] at this
  norm_num at this
def C630 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate630 : C630.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction630 : ¬ (C630.det = 0 ∧ ∀ i, C630.adjugate i i ≠ 0) := by
  intro h
  have := certificate630
  rw [h.1] at this
  norm_num at this
def C631 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate631 : C631.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction631 : ¬ (C631.det = 0 ∧ ∀ i, C631.adjugate i i ≠ 0) := by
  intro h
  have := certificate631
  rw [h.1] at this
  norm_num at this
def C632 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate632 : C632.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction632 : ¬ (C632.det = 0 ∧ ∀ i, C632.adjugate i i ≠ 0) := by
  intro h
  have := certificate632
  rw [h.1] at this
  norm_num at this
def C633 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate633 : C633.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction633 : ¬ (C633.det = 0 ∧ ∀ i, C633.adjugate i i ≠ 0) := by
  intro h
  have := certificate633
  rw [h.1] at this
  norm_num at this
def C634 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate634 : C634.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction634 : ¬ (C634.det = 0 ∧ ∀ i, C634.adjugate i i ≠ 0) := by
  intro h
  have := certificate634
  rw [h.1] at this
  norm_num at this
def C635 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate635 : C635.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction635 : ¬ (C635.det = 0 ∧ ∀ i, C635.adjugate i i ≠ 0) := by
  intro h
  have := certificate635
  rw [h.1] at this
  norm_num at this
def C636 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate636 : C636.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction636 : ¬ (C636.det = 0 ∧ ∀ i, C636.adjugate i i ≠ 0) := by
  intro h
  have := certificate636
  rw [h.1] at this
  norm_num at this
def C637 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate637 : C637.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction637 : ¬ (C637.det = 0 ∧ ∀ i, C637.adjugate i i ≠ 0) := by
  intro h
  have := certificate637
  rw [h.1] at this
  norm_num at this
def C638 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, 1]
theorem certificate638 : C638.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction638 : ¬ (C638.det = 0 ∧ ∀ i, C638.adjugate i i ≠ 0) := by
  intro h
  have := certificate638
  rw [h.1] at this
  norm_num at this
def C639 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -2, 0; 0, 0, 0, 0, 0, 2, 0, -1]
theorem certificate639 : C639.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction639 : ¬ (C639.det = 0 ∧ ∀ i, C639.adjugate i i ≠ 0) := by
  intro h
  have := certificate639
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0019
