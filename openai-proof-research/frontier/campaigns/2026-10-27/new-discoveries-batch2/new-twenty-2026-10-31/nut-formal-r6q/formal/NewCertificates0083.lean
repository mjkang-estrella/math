import VerifiedDet
namespace Nut8.NewCertificates0083
def C2656 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2656 : C2656.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2656 : ¬ (C2656.det = 0 ∧ ∀ i, C2656.adjugate i i ≠ 0) := by
  intro h
  have := certificate2656
  rw [h.1] at this
  norm_num at this
def C2657 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2657 : C2657.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2657 : ¬ (C2657.det = 0 ∧ ∀ i, C2657.adjugate i i ≠ 0) := by
  intro h
  have := certificate2657
  rw [h.1] at this
  norm_num at this
def C2658 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2658 : C2658.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2658 : ¬ (C2658.det = 0 ∧ ∀ i, C2658.adjugate i i ≠ 0) := by
  intro h
  have := certificate2658
  rw [h.1] at this
  norm_num at this
def C2659 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2659 : C2659.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2659 : ¬ (C2659.det = 0 ∧ ∀ i, C2659.adjugate i i ≠ 0) := by
  intro h
  have := certificate2659
  rw [h.1] at this
  norm_num at this
def C2660 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2660 : C2660.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2660 : ¬ (C2660.det = 0 ∧ ∀ i, C2660.adjugate i i ≠ 0) := by
  intro h
  have := certificate2660
  rw [h.1] at this
  norm_num at this
def C2661 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2661 : C2661.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2661 : ¬ (C2661.det = 0 ∧ ∀ i, C2661.adjugate i i ≠ 0) := by
  intro h
  have := certificate2661
  rw [h.1] at this
  norm_num at this
def C2662 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2662 : C2662.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2662 : ¬ (C2662.det = 0 ∧ ∀ i, C2662.adjugate i i ≠ 0) := by
  intro h
  have := certificate2662
  rw [h.1] at this
  norm_num at this
def C2663 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2663 : C2663.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2663 : ¬ (C2663.det = 0 ∧ ∀ i, C2663.adjugate i i ≠ 0) := by
  intro h
  have := certificate2663
  rw [h.1] at this
  norm_num at this
def C2664 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2664 : C2664.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2664 : ¬ (C2664.det = 0 ∧ ∀ i, C2664.adjugate i i ≠ 0) := by
  intro h
  have := certificate2664
  rw [h.1] at this
  norm_num at this
def C2665 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2665 : C2665.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2665 : ¬ (C2665.det = 0 ∧ ∀ i, C2665.adjugate i i ≠ 0) := by
  intro h
  have := certificate2665
  rw [h.1] at this
  norm_num at this
def C2666 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2666 : C2666.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2666 : ¬ (C2666.det = 0 ∧ ∀ i, C2666.adjugate i i ≠ 0) := by
  intro h
  have := certificate2666
  rw [h.1] at this
  norm_num at this
def C2667 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2667 : C2667.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2667 : ¬ (C2667.det = 0 ∧ ∀ i, C2667.adjugate i i ≠ 0) := by
  intro h
  have := certificate2667
  rw [h.1] at this
  norm_num at this
def C2668 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2668 : C2668.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2668 : ¬ (C2668.det = 0 ∧ ∀ i, C2668.adjugate i i ≠ 0) := by
  intro h
  have := certificate2668
  rw [h.1] at this
  norm_num at this
def C2669 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2669 : C2669.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2669 : ¬ (C2669.det = 0 ∧ ∀ i, C2669.adjugate i i ≠ 0) := by
  intro h
  have := certificate2669
  rw [h.1] at this
  norm_num at this
def C2670 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2670 : C2670.det = (-22 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2670 : ¬ (C2670.det = 0 ∧ ∀ i, C2670.adjugate i i ≠ 0) := by
  intro h
  have := certificate2670
  rw [h.1] at this
  norm_num at this
def C2671 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2671 : C2671.det = (-2 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2671 : ¬ (C2671.det = 0 ∧ ∀ i, C2671.adjugate i i ≠ 0) := by
  intro h
  have := certificate2671
  rw [h.1] at this
  norm_num at this
def C2672 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2672 : C2672.det = (14 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2672 : ¬ (C2672.det = 0 ∧ ∀ i, C2672.adjugate i i ≠ 0) := by
  intro h
  have := certificate2672
  rw [h.1] at this
  norm_num at this
def C2673 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2673 : C2673.det = (-6 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2673 : ¬ (C2673.det = 0 ∧ ∀ i, C2673.adjugate i i ≠ 0) := by
  intro h
  have := certificate2673
  rw [h.1] at this
  norm_num at this
def C2674 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2674 : C2674.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2674 : ¬ (C2674.det = 0 ∧ ∀ i, C2674.adjugate i i ≠ 0) := by
  intro h
  have := certificate2674
  rw [h.1] at this
  norm_num at this
def C2675 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2675 : C2675.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2675 : ¬ (C2675.det = 0 ∧ ∀ i, C2675.adjugate i i ≠ 0) := by
  intro h
  have := certificate2675
  rw [h.1] at this
  norm_num at this
def C2676 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2676 : C2676.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2676 : ¬ (C2676.det = 0 ∧ ∀ i, C2676.adjugate i i ≠ 0) := by
  intro h
  have := certificate2676
  rw [h.1] at this
  norm_num at this
def C2677 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2677 : C2677.det = (-50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2677 : ¬ (C2677.det = 0 ∧ ∀ i, C2677.adjugate i i ≠ 0) := by
  intro h
  have := certificate2677
  rw [h.1] at this
  norm_num at this
def C2678 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2678 : C2678.det = (-50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2678 : ¬ (C2678.det = 0 ∧ ∀ i, C2678.adjugate i i ≠ 0) := by
  intro h
  have := certificate2678
  rw [h.1] at this
  norm_num at this
def C2679 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2679 : C2679.det = (18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2679 : ¬ (C2679.det = 0 ∧ ∀ i, C2679.adjugate i i ≠ 0) := by
  intro h
  have := certificate2679
  rw [h.1] at this
  norm_num at this
def C2680 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2680 : C2680.det = (50 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2680 : ¬ (C2680.det = 0 ∧ ∀ i, C2680.adjugate i i ≠ 0) := by
  intro h
  have := certificate2680
  rw [h.1] at this
  norm_num at this
def C2681 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2681 : C2681.det = (-18 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2681 : ¬ (C2681.det = 0 ∧ ∀ i, C2681.adjugate i i ≠ 0) := by
  intro h
  have := certificate2681
  rw [h.1] at this
  norm_num at this
def C2682 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate2682 : C2682.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2682 : ¬ (C2682.det = 0 ∧ ∀ i, C2682.adjugate i i ≠ 0) := by
  intro h
  have := certificate2682
  rw [h.1] at this
  norm_num at this
def C2683 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate2683 : C2683.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2683 : ¬ (C2683.det = 0 ∧ ∀ i, C2683.adjugate i i ≠ 0) := by
  intro h
  have := certificate2683
  rw [h.1] at this
  norm_num at this
def C2684 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate2684 : C2684.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2684 : ¬ (C2684.det = 0 ∧ ∀ i, C2684.adjugate i i ≠ 0) := by
  intro h
  have := certificate2684
  rw [h.1] at this
  norm_num at this
def C2685 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate2685 : C2685.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2685 : ¬ (C2685.det = 0 ∧ ∀ i, C2685.adjugate i i ≠ 0) := by
  intro h
  have := certificate2685
  rw [h.1] at this
  norm_num at this
def C2686 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate2686 : C2686.det = (-68 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2686 : ¬ (C2686.det = 0 ∧ ∀ i, C2686.adjugate i i ≠ 0) := by
  intro h
  have := certificate2686
  rw [h.1] at this
  norm_num at this
def C2687 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate2687 : C2687.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2687 : ¬ (C2687.det = 0 ∧ ∀ i, C2687.adjugate i i ≠ 0) := by
  intro h
  have := certificate2687
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0083
