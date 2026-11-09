import VerifiedDet
namespace Nut8.NewCertificates0084
def C2688 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate2688 : C2688.det = (44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2688 : ¬ (C2688.det = 0 ∧ ∀ i, C2688.adjugate i i ≠ 0) := by
  intro h
  have := certificate2688
  rw [h.1] at this
  norm_num at this
def C2689 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate2689 : C2689.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2689 : ¬ (C2689.det = 0 ∧ ∀ i, C2689.adjugate i i ≠ 0) := by
  intro h
  have := certificate2689
  rw [h.1] at this
  norm_num at this
def C2690 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2690 : C2690.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2690 : ¬ (C2690.det = 0 ∧ ∀ i, C2690.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2690
def C2691 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2691 : C2691.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2691 : ¬ (C2691.det = 0 ∧ ∀ i, C2691.adjugate i i ≠ 0) := by
  intro h
  have := certificate2691
  rw [h.1] at this
  norm_num at this
def C2692 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2692 : C2692.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2692 : ¬ (C2692.det = 0 ∧ ∀ i, C2692.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2692
def C2693 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2693 : C2693.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2693 : ¬ (C2693.det = 0 ∧ ∀ i, C2693.adjugate i i ≠ 0) := by
  intro h
  have := certificate2693
  rw [h.1] at this
  norm_num at this
def C2694 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2694 : C2694.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2694 : ¬ (C2694.det = 0 ∧ ∀ i, C2694.adjugate i i ≠ 0) := by
  intro h
  have := certificate2694
  rw [h.1] at this
  norm_num at this
def C2695 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2695 : C2695.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2695 : ¬ (C2695.det = 0 ∧ ∀ i, C2695.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2695
def C2696 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2696 : C2696.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2696 : ¬ (C2696.det = 0 ∧ ∀ i, C2696.adjugate i i ≠ 0) := by
  intro h
  have := certificate2696
  rw [h.1] at this
  norm_num at this
def C2697 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2697 : C2697.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction2697 : ¬ (C2697.det = 0 ∧ ∀ i, C2697.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate2697
def C2698 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2698 : C2698.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2698 : ¬ (C2698.det = 0 ∧ ∀ i, C2698.adjugate i i ≠ 0) := by
  intro h
  have := certificate2698
  rw [h.1] at this
  norm_num at this
def C2699 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2699 : C2699.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2699 : ¬ (C2699.det = 0 ∧ ∀ i, C2699.adjugate i i ≠ 0) := by
  intro h
  have := certificate2699
  rw [h.1] at this
  norm_num at this
def C2700 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2700 : C2700.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2700 : ¬ (C2700.det = 0 ∧ ∀ i, C2700.adjugate i i ≠ 0) := by
  intro h
  have := certificate2700
  rw [h.1] at this
  norm_num at this
def C2701 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate2701 : C2701.det = (96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2701 : ¬ (C2701.det = 0 ∧ ∀ i, C2701.adjugate i i ≠ 0) := by
  intro h
  have := certificate2701
  rw [h.1] at this
  norm_num at this
def C2702 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2702 : C2702.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2702 : ¬ (C2702.det = 0 ∧ ∀ i, C2702.adjugate i i ≠ 0) := by
  intro h
  have := certificate2702
  rw [h.1] at this
  norm_num at this
def C2703 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2703 : C2703.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2703 : ¬ (C2703.det = 0 ∧ ∀ i, C2703.adjugate i i ≠ 0) := by
  intro h
  have := certificate2703
  rw [h.1] at this
  norm_num at this
def C2704 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2704 : C2704.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2704 : ¬ (C2704.det = 0 ∧ ∀ i, C2704.adjugate i i ≠ 0) := by
  intro h
  have := certificate2704
  rw [h.1] at this
  norm_num at this
def C2705 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2705 : C2705.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2705 : ¬ (C2705.det = 0 ∧ ∀ i, C2705.adjugate i i ≠ 0) := by
  intro h
  have := certificate2705
  rw [h.1] at this
  norm_num at this
def C2706 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2706 : C2706.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2706 : ¬ (C2706.det = 0 ∧ ∀ i, C2706.adjugate i i ≠ 0) := by
  intro h
  have := certificate2706
  rw [h.1] at this
  norm_num at this
def C2707 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2707 : C2707.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2707 : ¬ (C2707.det = 0 ∧ ∀ i, C2707.adjugate i i ≠ 0) := by
  intro h
  have := certificate2707
  rw [h.1] at this
  norm_num at this
def C2708 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2708 : C2708.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2708 : ¬ (C2708.det = 0 ∧ ∀ i, C2708.adjugate i i ≠ 0) := by
  intro h
  have := certificate2708
  rw [h.1] at this
  norm_num at this
def C2709 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2709 : C2709.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2709 : ¬ (C2709.det = 0 ∧ ∀ i, C2709.adjugate i i ≠ 0) := by
  intro h
  have := certificate2709
  rw [h.1] at this
  norm_num at this
def C2710 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2710 : C2710.det = (-17 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2710 : ¬ (C2710.det = 0 ∧ ∀ i, C2710.adjugate i i ≠ 0) := by
  intro h
  have := certificate2710
  rw [h.1] at this
  norm_num at this
def C2711 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2711 : C2711.det = (15 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2711 : ¬ (C2711.det = 0 ∧ ∀ i, C2711.adjugate i i ≠ 0) := by
  intro h
  have := certificate2711
  rw [h.1] at this
  norm_num at this
def C2712 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate2712 : C2712.det = (7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2712 : ¬ (C2712.det = 0 ∧ ∀ i, C2712.adjugate i i ≠ 0) := by
  intro h
  have := certificate2712
  rw [h.1] at this
  norm_num at this
def C2713 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate2713 : C2713.det = (-25 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2713 : ¬ (C2713.det = 0 ∧ ∀ i, C2713.adjugate i i ≠ 0) := by
  intro h
  have := certificate2713
  rw [h.1] at this
  norm_num at this
def C2714 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2714 : C2714.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2714 : ¬ (C2714.det = 0 ∧ ∀ i, C2714.adjugate i i ≠ 0) := by
  intro h
  have := certificate2714
  rw [h.1] at this
  norm_num at this
def C2715 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2715 : C2715.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2715 : ¬ (C2715.det = 0 ∧ ∀ i, C2715.adjugate i i ≠ 0) := by
  intro h
  have := certificate2715
  rw [h.1] at this
  norm_num at this
def C2716 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate2716 : C2716.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2716 : ¬ (C2716.det = 0 ∧ ∀ i, C2716.adjugate i i ≠ 0) := by
  intro h
  have := certificate2716
  rw [h.1] at this
  norm_num at this
def C2717 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate2717 : C2717.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2717 : ¬ (C2717.det = 0 ∧ ∀ i, C2717.adjugate i i ≠ 0) := by
  intro h
  have := certificate2717
  rw [h.1] at this
  norm_num at this
def C2718 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2718 : C2718.det = (-9 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2718 : ¬ (C2718.det = 0 ∧ ∀ i, C2718.adjugate i i ≠ 0) := by
  intro h
  have := certificate2718
  rw [h.1] at this
  norm_num at this
def C2719 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate2719 : C2719.det = (-1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction2719 : ¬ (C2719.det = 0 ∧ ∀ i, C2719.adjugate i i ≠ 0) := by
  intro h
  have := certificate2719
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0084
