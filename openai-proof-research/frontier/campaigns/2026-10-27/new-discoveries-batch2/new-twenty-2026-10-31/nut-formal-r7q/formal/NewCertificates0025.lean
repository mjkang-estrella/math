import VerifiedDet
namespace Nut8.NewCertificates0025
def C800 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate800 : C800.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction800 : ¬ (C800.det = 0 ∧ ∀ i, C800.adjugate i i ≠ 0) := by
  intro h
  have := certificate800
  rw [h.1] at this
  norm_num at this
def C801 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate801 : C801.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction801 : ¬ (C801.det = 0 ∧ ∀ i, C801.adjugate i i ≠ 0) := by
  intro h
  have := certificate801
  rw [h.1] at this
  norm_num at this
def C802 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate802 : C802.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction802 : ¬ (C802.det = 0 ∧ ∀ i, C802.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate802
def C803 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate803 : C803.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction803 : ¬ (C803.det = 0 ∧ ∀ i, C803.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate803
def C804 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate804 : C804.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction804 : ¬ (C804.det = 0 ∧ ∀ i, C804.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate804
def C805 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate805 : C805.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction805 : ¬ (C805.det = 0 ∧ ∀ i, C805.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate805
def C806 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate806 : C806.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction806 : ¬ (C806.det = 0 ∧ ∀ i, C806.adjugate i i ≠ 0) := by
  intro h
  have := certificate806
  rw [h.1] at this
  norm_num at this
def C807 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate807 : C807.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction807 : ¬ (C807.det = 0 ∧ ∀ i, C807.adjugate i i ≠ 0) := by
  intro h
  have := certificate807
  rw [h.1] at this
  norm_num at this
def C808 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate808 : C808.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction808 : ¬ (C808.det = 0 ∧ ∀ i, C808.adjugate i i ≠ 0) := by
  intro h
  have := certificate808
  rw [h.1] at this
  norm_num at this
def C809 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate809 : C809.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction809 : ¬ (C809.det = 0 ∧ ∀ i, C809.adjugate i i ≠ 0) := by
  intro h
  have := certificate809
  rw [h.1] at this
  norm_num at this
def C810 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate810 : C810.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction810 : ¬ (C810.det = 0 ∧ ∀ i, C810.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate810
def C811 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate811 : C811.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction811 : ¬ (C811.det = 0 ∧ ∀ i, C811.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate811
def C812 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate812 : C812.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction812 : ¬ (C812.det = 0 ∧ ∀ i, C812.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate812
def C813 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate813 : C813.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction813 : ¬ (C813.det = 0 ∧ ∀ i, C813.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate813
def C814 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate814 : C814.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction814 : ¬ (C814.det = 0 ∧ ∀ i, C814.adjugate i i ≠ 0) := by
  intro h
  have := certificate814
  rw [h.1] at this
  norm_num at this
def C815 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate815 : C815.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction815 : ¬ (C815.det = 0 ∧ ∀ i, C815.adjugate i i ≠ 0) := by
  intro h
  have := certificate815
  rw [h.1] at this
  norm_num at this
def C816 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate816 : C816.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction816 : ¬ (C816.det = 0 ∧ ∀ i, C816.adjugate i i ≠ 0) := by
  intro h
  have := certificate816
  rw [h.1] at this
  norm_num at this
def C817 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate817 : C817.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction817 : ¬ (C817.det = 0 ∧ ∀ i, C817.adjugate i i ≠ 0) := by
  intro h
  have := certificate817
  rw [h.1] at this
  norm_num at this
def C818 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate818 : C818.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction818 : ¬ (C818.det = 0 ∧ ∀ i, C818.adjugate i i ≠ 0) := by
  intro h
  have := certificate818
  rw [h.1] at this
  norm_num at this
def C819 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate819 : C819.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction819 : ¬ (C819.det = 0 ∧ ∀ i, C819.adjugate i i ≠ 0) := by
  intro h
  have := certificate819
  rw [h.1] at this
  norm_num at this
def C820 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate820 : C820.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction820 : ¬ (C820.det = 0 ∧ ∀ i, C820.adjugate i i ≠ 0) := by
  intro h
  have := certificate820
  rw [h.1] at this
  norm_num at this
def C821 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate821 : C821.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction821 : ¬ (C821.det = 0 ∧ ∀ i, C821.adjugate i i ≠ 0) := by
  intro h
  have := certificate821
  rw [h.1] at this
  norm_num at this
def C822 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate822 : C822.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction822 : ¬ (C822.det = 0 ∧ ∀ i, C822.adjugate i i ≠ 0) := by
  intro h
  have := certificate822
  rw [h.1] at this
  norm_num at this
def C823 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 2, 0; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 2, 0, 0, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate823 : C823.det = (-96 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction823 : ¬ (C823.det = 0 ∧ ∀ i, C823.adjugate i i ≠ 0) := by
  intro h
  have := certificate823
  rw [h.1] at this
  norm_num at this
def C824 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate824 : C824.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction824 : ¬ (C824.det = 0 ∧ ∀ i, C824.adjugate i i ≠ 0) := by
  intro h
  have := certificate824
  rw [h.1] at this
  norm_num at this
def C825 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate825 : C825.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction825 : ¬ (C825.det = 0 ∧ ∀ i, C825.adjugate i i ≠ 0) := by
  intro h
  have := certificate825
  rw [h.1] at this
  norm_num at this
def C826 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate826 : C826.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction826 : ¬ (C826.det = 0 ∧ ∀ i, C826.adjugate i i ≠ 0) := by
  intro h
  have := certificate826
  rw [h.1] at this
  norm_num at this
def C827 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate827 : C827.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction827 : ¬ (C827.det = 0 ∧ ∀ i, C827.adjugate i i ≠ 0) := by
  intro h
  have := certificate827
  rw [h.1] at this
  norm_num at this
def C828 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate828 : C828.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction828 : ¬ (C828.det = 0 ∧ ∀ i, C828.adjugate i i ≠ 0) := by
  intro h
  have := certificate828
  rw [h.1] at this
  norm_num at this
def C829 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate829 : C829.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction829 : ¬ (C829.det = 0 ∧ ∀ i, C829.adjugate i i ≠ 0) := by
  intro h
  have := certificate829
  rw [h.1] at this
  norm_num at this
def C830 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate830 : C830.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction830 : ¬ (C830.det = 0 ∧ ∀ i, C830.adjugate i i ≠ 0) := by
  intro h
  have := certificate830
  rw [h.1] at this
  norm_num at this
def C831 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate831 : C831.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction831 : ¬ (C831.det = 0 ∧ ∀ i, C831.adjugate i i ≠ 0) := by
  intro h
  have := certificate831
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0025
