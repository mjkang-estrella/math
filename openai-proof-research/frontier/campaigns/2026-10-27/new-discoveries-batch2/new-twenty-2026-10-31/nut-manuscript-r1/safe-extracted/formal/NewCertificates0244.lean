import VerifiedDet
namespace Nut8.NewCertificates0244
def C7808 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7808 : C7808.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7808 : ¬ (C7808.det = 0 ∧ ∀ i, C7808.adjugate i i ≠ 0) := by
  intro h
  have := certificate7808
  rw [h.1] at this
  norm_num at this
def C7809 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7809 : C7809.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7809 : ¬ (C7809.det = 0 ∧ ∀ i, C7809.adjugate i i ≠ 0) := by
  intro h
  have := certificate7809
  rw [h.1] at this
  norm_num at this
def C7810 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7810 : C7810.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7810 : ¬ (C7810.det = 0 ∧ ∀ i, C7810.adjugate i i ≠ 0) := by
  intro h
  have := certificate7810
  rw [h.1] at this
  norm_num at this
def C7811 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7811 : C7811.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7811 : ¬ (C7811.det = 0 ∧ ∀ i, C7811.adjugate i i ≠ 0) := by
  intro h
  have := certificate7811
  rw [h.1] at this
  norm_num at this
def C7812 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7812 : C7812.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7812 : ¬ (C7812.det = 0 ∧ ∀ i, C7812.adjugate i i ≠ 0) := by
  intro h
  have := certificate7812
  rw [h.1] at this
  norm_num at this
def C7813 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7813 : C7813.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7813 : ¬ (C7813.det = 0 ∧ ∀ i, C7813.adjugate i i ≠ 0) := by
  intro h
  have := certificate7813
  rw [h.1] at this
  norm_num at this
def C7814 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7814 : C7814.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7814 : ¬ (C7814.det = 0 ∧ ∀ i, C7814.adjugate i i ≠ 0) := by
  intro h
  have := certificate7814
  rw [h.1] at this
  norm_num at this
def C7815 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7815 : C7815.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7815 : ¬ (C7815.det = 0 ∧ ∀ i, C7815.adjugate i i ≠ 0) := by
  intro h
  have := certificate7815
  rw [h.1] at this
  norm_num at this
def C7816 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7816 : C7816.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7816 : ¬ (C7816.det = 0 ∧ ∀ i, C7816.adjugate i i ≠ 0) := by
  intro h
  have := certificate7816
  rw [h.1] at this
  norm_num at this
def C7817 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7817 : C7817.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7817 : ¬ (C7817.det = 0 ∧ ∀ i, C7817.adjugate i i ≠ 0) := by
  intro h
  have := certificate7817
  rw [h.1] at this
  norm_num at this
def C7818 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7818 : C7818.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7818 : ¬ (C7818.det = 0 ∧ ∀ i, C7818.adjugate i i ≠ 0) := by
  intro h
  have := certificate7818
  rw [h.1] at this
  norm_num at this
def C7819 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7819 : C7819.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7819 : ¬ (C7819.det = 0 ∧ ∀ i, C7819.adjugate i i ≠ 0) := by
  intro h
  have := certificate7819
  rw [h.1] at this
  norm_num at this
def C7820 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7820 : C7820.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7820 : ¬ (C7820.det = 0 ∧ ∀ i, C7820.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7820
def C7821 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7821 : C7821.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7821 : ¬ (C7821.det = 0 ∧ ∀ i, C7821.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7821
def C7822 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7822 : C7822.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7822 : ¬ (C7822.det = 0 ∧ ∀ i, C7822.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7822
def C7823 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7823 : C7823.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7823 : ¬ (C7823.det = 0 ∧ ∀ i, C7823.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7823
def C7824 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7824 : C7824.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7824 : ¬ (C7824.det = 0 ∧ ∀ i, C7824.adjugate i i ≠ 0) := by
  intro h
  have := certificate7824
  rw [h.1] at this
  norm_num at this
def C7825 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7825 : C7825.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7825 : ¬ (C7825.det = 0 ∧ ∀ i, C7825.adjugate i i ≠ 0) := by
  intro h
  have := certificate7825
  rw [h.1] at this
  norm_num at this
def C7826 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7826 : C7826.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7826 : ¬ (C7826.det = 0 ∧ ∀ i, C7826.adjugate i i ≠ 0) := by
  intro h
  have := certificate7826
  rw [h.1] at this
  norm_num at this
def C7827 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7827 : C7827.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7827 : ¬ (C7827.det = 0 ∧ ∀ i, C7827.adjugate i i ≠ 0) := by
  intro h
  have := certificate7827
  rw [h.1] at this
  norm_num at this
def C7828 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7828 : C7828.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7828 : ¬ (C7828.det = 0 ∧ ∀ i, C7828.adjugate i i ≠ 0) := by
  intro h
  have := certificate7828
  rw [h.1] at this
  norm_num at this
def C7829 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7829 : C7829.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7829 : ¬ (C7829.det = 0 ∧ ∀ i, C7829.adjugate i i ≠ 0) := by
  intro h
  have := certificate7829
  rw [h.1] at this
  norm_num at this
def C7830 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7830 : C7830.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7830 : ¬ (C7830.det = 0 ∧ ∀ i, C7830.adjugate i i ≠ 0) := by
  intro h
  have := certificate7830
  rw [h.1] at this
  norm_num at this
def C7831 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7831 : C7831.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7831 : ¬ (C7831.det = 0 ∧ ∀ i, C7831.adjugate i i ≠ 0) := by
  intro h
  have := certificate7831
  rw [h.1] at this
  norm_num at this
def C7832 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7832 : C7832.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7832 : ¬ (C7832.det = 0 ∧ ∀ i, C7832.adjugate i i ≠ 0) := by
  intro h
  have := certificate7832
  rw [h.1] at this
  norm_num at this
def C7833 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7833 : C7833.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7833 : ¬ (C7833.det = 0 ∧ ∀ i, C7833.adjugate i i ≠ 0) := by
  intro h
  have := certificate7833
  rw [h.1] at this
  norm_num at this
def C7834 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7834 : C7834.det = (64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7834 : ¬ (C7834.det = 0 ∧ ∀ i, C7834.adjugate i i ≠ 0) := by
  intro h
  have := certificate7834
  rw [h.1] at this
  norm_num at this
def C7835 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7835 : C7835.det = (-64 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7835 : ¬ (C7835.det = 0 ∧ ∀ i, C7835.adjugate i i ≠ 0) := by
  intro h
  have := certificate7835
  rw [h.1] at this
  norm_num at this
def C7836 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1]
theorem certificate7836 : C7836.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7836 : ¬ (C7836.det = 0 ∧ ∀ i, C7836.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7836
def C7837 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, 1, 0, -1]
theorem certificate7837 : C7837.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction7837 : ¬ (C7837.det = 0 ∧ ∀ i, C7837.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate7837
def C7838 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, -1, 0, 1]
theorem certificate7838 : C7838.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7838 : ¬ (C7838.det = 0 ∧ ∀ i, C7838.adjugate i i ≠ 0) := by
  intro h
  have := certificate7838
  rw [h.1] at this
  norm_num at this
def C7839 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, -1, 0; 0, 0, 0, 0, 1, -1, 0, -1]
theorem certificate7839 : C7839.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction7839 : ¬ (C7839.det = 0 ∧ ∀ i, C7839.adjugate i i ≠ 0) := by
  intro h
  have := certificate7839
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0244
