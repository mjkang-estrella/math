import VerifiedDet
namespace Nut8.NewCertificates0240
def C7680 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate7680 : C7680.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7680 : ¬ (C7680.det = 0 ∧ ∀ i, C7680.adjugate i i ≠ 0) := by
  intro h
  have := certificate7680
  rw [h.1] at this
  norm_num at this
def C7681 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, 1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate7681 : C7681.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7681 : ¬ (C7681.det = 0 ∧ ∀ i, C7681.adjugate i i ≠ 0) := by
  intro h
  have := certificate7681
  rw [h.1] at this
  norm_num at this
def C7682 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate7682 : C7682.det = (9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7682 : ¬ (C7682.det = 0 ∧ ∀ i, C7682.adjugate i i ≠ 0) := by
  intro h
  have := certificate7682
  rw [h.1] at this
  norm_num at this
def C7683 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, -1, 1, 0; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, -1, 0, 0, 0, 0, -1; 0, 0, 1, -1, 0, 0, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate7683 : C7683.det = (81 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7683 : ¬ (C7683.det = 0 ∧ ∀ i, C7683.adjugate i i ≠ 0) := by
  intro h
  have := certificate7683
  rw [h.1] at this
  norm_num at this
def C7684 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7684 : C7684.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7684 : ¬ (C7684.det = 0 ∧ ∀ i, C7684.adjugate i i ≠ 0) := by
  intro h
  have := certificate7684
  rw [h.1] at this
  norm_num at this
def C7685 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7685 : C7685.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7685 : ¬ (C7685.det = 0 ∧ ∀ i, C7685.adjugate i i ≠ 0) := by
  intro h
  have := certificate7685
  rw [h.1] at this
  norm_num at this
def C7686 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7686 : C7686.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7686 : ¬ (C7686.det = 0 ∧ ∀ i, C7686.adjugate i i ≠ 0) := by
  intro h
  have := certificate7686
  rw [h.1] at this
  norm_num at this
def C7687 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7687 : C7687.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7687 : ¬ (C7687.det = 0 ∧ ∀ i, C7687.adjugate i i ≠ 0) := by
  intro h
  have := certificate7687
  rw [h.1] at this
  norm_num at this
def C7688 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7688 : C7688.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7688 : ¬ (C7688.det = 0 ∧ ∀ i, C7688.adjugate i i ≠ 0) := by
  intro h
  have := certificate7688
  rw [h.1] at this
  norm_num at this
def C7689 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7689 : C7689.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7689 : ¬ (C7689.det = 0 ∧ ∀ i, C7689.adjugate i i ≠ 0) := by
  intro h
  have := certificate7689
  rw [h.1] at this
  norm_num at this
def C7690 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7690 : C7690.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7690 : ¬ (C7690.det = 0 ∧ ∀ i, C7690.adjugate i i ≠ 0) := by
  intro h
  have := certificate7690
  rw [h.1] at this
  norm_num at this
def C7691 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7691 : C7691.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7691 : ¬ (C7691.det = 0 ∧ ∀ i, C7691.adjugate i i ≠ 0) := by
  intro h
  have := certificate7691
  rw [h.1] at this
  norm_num at this
def C7692 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7692 : C7692.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7692 : ¬ (C7692.det = 0 ∧ ∀ i, C7692.adjugate i i ≠ 0) := by
  intro h
  have := certificate7692
  rw [h.1] at this
  norm_num at this
def C7693 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7693 : C7693.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7693 : ¬ (C7693.det = 0 ∧ ∀ i, C7693.adjugate i i ≠ 0) := by
  intro h
  have := certificate7693
  rw [h.1] at this
  norm_num at this
def C7694 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7694 : C7694.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7694 : ¬ (C7694.det = 0 ∧ ∀ i, C7694.adjugate i i ≠ 0) := by
  intro h
  have := certificate7694
  rw [h.1] at this
  norm_num at this
def C7695 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7695 : C7695.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7695 : ¬ (C7695.det = 0 ∧ ∀ i, C7695.adjugate i i ≠ 0) := by
  intro h
  have := certificate7695
  rw [h.1] at this
  norm_num at this
def C7696 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7696 : C7696.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7696 : ¬ (C7696.det = 0 ∧ ∀ i, C7696.adjugate i i ≠ 0) := by
  intro h
  have := certificate7696
  rw [h.1] at this
  norm_num at this
def C7697 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7697 : C7697.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7697 : ¬ (C7697.det = 0 ∧ ∀ i, C7697.adjugate i i ≠ 0) := by
  intro h
  have := certificate7697
  rw [h.1] at this
  norm_num at this
def C7698 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7698 : C7698.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7698 : ¬ (C7698.det = 0 ∧ ∀ i, C7698.adjugate i i ≠ 0) := by
  intro h
  have := certificate7698
  rw [h.1] at this
  norm_num at this
def C7699 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 0, -1, 0; 0, 1, 0, 1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7699 : C7699.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7699 : ¬ (C7699.det = 0 ∧ ∀ i, C7699.adjugate i i ≠ 0) := by
  intro h
  have := certificate7699
  rw [h.1] at this
  norm_num at this
def C7700 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7700 : C7700.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7700 : ¬ (C7700.det = 0 ∧ ∀ i, C7700.adjugate i i ≠ 0) := by
  intro h
  have := certificate7700
  rw [h.1] at this
  norm_num at this
def C7701 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7701 : C7701.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7701 : ¬ (C7701.det = 0 ∧ ∀ i, C7701.adjugate i i ≠ 0) := by
  intro h
  have := certificate7701
  rw [h.1] at this
  norm_num at this
def C7702 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7702 : C7702.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7702 : ¬ (C7702.det = 0 ∧ ∀ i, C7702.adjugate i i ≠ 0) := by
  intro h
  have := certificate7702
  rw [h.1] at this
  norm_num at this
def C7703 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7703 : C7703.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7703 : ¬ (C7703.det = 0 ∧ ∀ i, C7703.adjugate i i ≠ 0) := by
  intro h
  have := certificate7703
  rw [h.1] at this
  norm_num at this
def C7704 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7704 : C7704.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7704 : ¬ (C7704.det = 0 ∧ ∀ i, C7704.adjugate i i ≠ 0) := by
  intro h
  have := certificate7704
  rw [h.1] at this
  norm_num at this
def C7705 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7705 : C7705.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7705 : ¬ (C7705.det = 0 ∧ ∀ i, C7705.adjugate i i ≠ 0) := by
  intro h
  have := certificate7705
  rw [h.1] at this
  norm_num at this
def C7706 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, 1, 0, 0]
theorem certificate7706 : C7706.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7706 : ¬ (C7706.det = 0 ∧ ∀ i, C7706.adjugate i i ≠ 0) := by
  intro h
  have := certificate7706
  rw [h.1] at this
  norm_num at this
def C7707 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, 1, 0; 0, 1, 0, -1, 0, 0, 0, -1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, 1, 0, -1, 0, 0; 0, 0, 1, 0, -1, -1, 0, 0]
theorem certificate7707 : C7707.det = (5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7707 : ¬ (C7707.det = 0 ∧ ∀ i, C7707.adjugate i i ≠ 0) := by
  intro h
  have := certificate7707
  rw [h.1] at this
  norm_num at this
def C7708 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7708 : C7708.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7708 : ¬ (C7708.det = 0 ∧ ∀ i, C7708.adjugate i i ≠ 0) := by
  intro h
  have := certificate7708
  rw [h.1] at this
  norm_num at this
def C7709 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, -1; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7709 : C7709.det = (45 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7709 : ¬ (C7709.det = 0 ∧ ∀ i, C7709.adjugate i i ≠ 0) := by
  intro h
  have := certificate7709
  rw [h.1] at this
  norm_num at this
def C7710 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, 1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
theorem certificate7710 : C7710.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7710 : ¬ (C7710.det = 0 ∧ ∀ i, C7710.adjugate i i ≠ 0) := by
  intro h
  have := certificate7710
  rw [h.1] at this
  norm_num at this
def C7711 : Matrix (Fin 8) (Fin 8) ℤ := !![0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, -1, 0, -1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -1, -1; 0, 0, 1, -1, 0, -1, 0, 0; 0, 0, 1, 0, 1, -1, 0, 0]
theorem certificate7711 : C7711.det = (13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7711 : ¬ (C7711.det = 0 ∧ ∀ i, C7711.adjugate i i ≠ 0) := by
  intro h
  have := certificate7711
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0240
