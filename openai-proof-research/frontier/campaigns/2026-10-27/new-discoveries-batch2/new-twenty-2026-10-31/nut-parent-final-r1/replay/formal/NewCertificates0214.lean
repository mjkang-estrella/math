import VerifiedDet
namespace Nut8.NewCertificates0214
def C6848 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6848 : C6848.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6848 : ¬ (C6848.det = 0 ∧ ∀ i, C6848.adjugate i i ≠ 0) := by
  intro h
  have := certificate6848
  rw [h.1] at this
  norm_num at this
def C6849 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6849 : C6849.det = (-53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6849 : ¬ (C6849.det = 0 ∧ ∀ i, C6849.adjugate i i ≠ 0) := by
  intro h
  have := certificate6849
  rw [h.1] at this
  norm_num at this
def C6850 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, 1]
theorem certificate6850 : C6850.det = (-53 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6850 : ¬ (C6850.det = 0 ∧ ∀ i, C6850.adjugate i i ≠ 0) := by
  intro h
  have := certificate6850
  rw [h.1] at this
  norm_num at this
def C6851 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, -1, 0, 0; 0, 0, 0, 1, -1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 0, 0, 2, -1]
theorem certificate6851 : C6851.det = (27 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6851 : ¬ (C6851.det = 0 ∧ ∀ i, C6851.adjugate i i ≠ 0) := by
  intro h
  have := certificate6851
  rw [h.1] at this
  norm_num at this
def C6852 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6852 : C6852.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6852 : ¬ (C6852.det = 0 ∧ ∀ i, C6852.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6852
def C6853 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6853 : C6853.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6853 : ¬ (C6853.det = 0 ∧ ∀ i, C6853.adjugate i i ≠ 0) := by
  intro h
  have := certificate6853
  rw [h.1] at this
  norm_num at this
def C6854 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6854 : C6854.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6854 : ¬ (C6854.det = 0 ∧ ∀ i, C6854.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6854
def C6855 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6855 : C6855.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6855 : ¬ (C6855.det = 0 ∧ ∀ i, C6855.adjugate i i ≠ 0) := by
  intro h
  have := certificate6855
  rw [h.1] at this
  norm_num at this
def C6856 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6856 : C6856.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6856 : ¬ (C6856.det = 0 ∧ ∀ i, C6856.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6856
def C6857 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6857 : C6857.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6857 : ¬ (C6857.det = 0 ∧ ∀ i, C6857.adjugate i i ≠ 0) := by
  intro h
  have := certificate6857
  rw [h.1] at this
  norm_num at this
def C6858 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1]
theorem certificate6858 : C6858.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6858 : ¬ (C6858.det = 0 ∧ ∀ i, C6858.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6858
def C6859 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, 1; 0, 0, 0, 0, 1, 0, 1, -1]
theorem certificate6859 : C6859.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6859 : ¬ (C6859.det = 0 ∧ ∀ i, C6859.adjugate i i ≠ 0) := by
  intro h
  have := certificate6859
  rw [h.1] at this
  norm_num at this
def C6860 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6860 : C6860.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6860 : ¬ (C6860.det = 0 ∧ ∀ i, C6860.adjugate i i ≠ 0) := by
  intro h
  have := certificate6860
  rw [h.1] at this
  norm_num at this
def C6861 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6861 : C6861.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6861 : ¬ (C6861.det = 0 ∧ ∀ i, C6861.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6861
def C6862 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6862 : C6862.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6862 : ¬ (C6862.det = 0 ∧ ∀ i, C6862.adjugate i i ≠ 0) := by
  intro h
  have := certificate6862
  rw [h.1] at this
  norm_num at this
def C6863 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6863 : C6863.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6863 : ¬ (C6863.det = 0 ∧ ∀ i, C6863.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6863
def C6864 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6864 : C6864.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6864 : ¬ (C6864.det = 0 ∧ ∀ i, C6864.adjugate i i ≠ 0) := by
  intro h
  have := certificate6864
  rw [h.1] at this
  norm_num at this
def C6865 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6865 : C6865.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6865 : ¬ (C6865.det = 0 ∧ ∀ i, C6865.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6865
def C6866 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 1, -1; 0, 0, 0, 0, 1, 0, -1, 1]
theorem certificate6866 : C6866.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6866 : ¬ (C6866.det = 0 ∧ ∀ i, C6866.adjugate i i ≠ 0) := by
  intro h
  have := certificate6866
  rw [h.1] at this
  norm_num at this
def C6867 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, -1, -1; 0, 0, 0, 0, 1, 0, -1, -1]
theorem certificate6867 : C6867.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction6867 : ¬ (C6867.det = 0 ∧ ∀ i, C6867.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate6867
def C6868 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6868 : C6868.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6868 : ¬ (C6868.det = 0 ∧ ∀ i, C6868.adjugate i i ≠ 0) := by
  intro h
  have := certificate6868
  rw [h.1] at this
  norm_num at this
def C6869 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6869 : C6869.det = (84 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6869 : ¬ (C6869.det = 0 ∧ ∀ i, C6869.adjugate i i ≠ 0) := by
  intro h
  have := certificate6869
  rw [h.1] at this
  norm_num at this
def C6870 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6870 : C6870.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6870 : ¬ (C6870.det = 0 ∧ ∀ i, C6870.adjugate i i ≠ 0) := by
  intro h
  have := certificate6870
  rw [h.1] at this
  norm_num at this
def C6871 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6871 : C6871.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6871 : ¬ (C6871.det = 0 ∧ ∀ i, C6871.adjugate i i ≠ 0) := by
  intro h
  have := certificate6871
  rw [h.1] at this
  norm_num at this
def C6872 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6872 : C6872.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6872 : ¬ (C6872.det = 0 ∧ ∀ i, C6872.adjugate i i ≠ 0) := by
  intro h
  have := certificate6872
  rw [h.1] at this
  norm_num at this
def C6873 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6873 : C6873.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6873 : ¬ (C6873.det = 0 ∧ ∀ i, C6873.adjugate i i ≠ 0) := by
  intro h
  have := certificate6873
  rw [h.1] at this
  norm_num at this
def C6874 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6874 : C6874.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6874 : ¬ (C6874.det = 0 ∧ ∀ i, C6874.adjugate i i ≠ 0) := by
  intro h
  have := certificate6874
  rw [h.1] at this
  norm_num at this
def C6875 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0]
theorem certificate6875 : C6875.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6875 : ¬ (C6875.det = 0 ∧ ∀ i, C6875.adjugate i i ≠ 0) := by
  intro h
  have := certificate6875
  rw [h.1] at this
  norm_num at this
def C6876 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6876 : C6876.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6876 : ¬ (C6876.det = 0 ∧ ∀ i, C6876.adjugate i i ≠ 0) := by
  intro h
  have := certificate6876
  rw [h.1] at this
  norm_num at this
def C6877 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6877 : C6877.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6877 : ¬ (C6877.det = 0 ∧ ∀ i, C6877.adjugate i i ≠ 0) := by
  intro h
  have := certificate6877
  rw [h.1] at this
  norm_num at this
def C6878 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6878 : C6878.det = (-44 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6878 : ¬ (C6878.det = 0 ∧ ∀ i, C6878.adjugate i i ≠ 0) := by
  intro h
  have := certificate6878
  rw [h.1] at this
  norm_num at this
def C6879 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, -1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, -2, 0, 0; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 1, 0, -2, 0]
theorem certificate6879 : C6879.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction6879 : ¬ (C6879.det = 0 ∧ ∀ i, C6879.adjugate i i ≠ 0) := by
  intro h
  have := certificate6879
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0214
