import VerifiedDet
namespace Nut8.NewCertificates0027
def C864 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate864 : C864.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction864 : ¬ (C864.det = 0 ∧ ∀ i, C864.adjugate i i ≠ 0) := by
  intro h
  have := certificate864
  rw [h.1] at this
  norm_num at this
def C865 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate865 : C865.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction865 : ¬ (C865.det = 0 ∧ ∀ i, C865.adjugate i i ≠ 0) := by
  intro h
  have := certificate865
  rw [h.1] at this
  norm_num at this
def C866 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate866 : C866.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction866 : ¬ (C866.det = 0 ∧ ∀ i, C866.adjugate i i ≠ 0) := by
  intro h
  have := certificate866
  rw [h.1] at this
  norm_num at this
def C867 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate867 : C867.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction867 : ¬ (C867.det = 0 ∧ ∀ i, C867.adjugate i i ≠ 0) := by
  intro h
  have := certificate867
  rw [h.1] at this
  norm_num at this
def C868 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate868 : C868.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction868 : ¬ (C868.det = 0 ∧ ∀ i, C868.adjugate i i ≠ 0) := by
  intro h
  have := certificate868
  rw [h.1] at this
  norm_num at this
def C869 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate869 : C869.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction869 : ¬ (C869.det = 0 ∧ ∀ i, C869.adjugate i i ≠ 0) := by
  intro h
  have := certificate869
  rw [h.1] at this
  norm_num at this
def C870 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate870 : C870.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction870 : ¬ (C870.det = 0 ∧ ∀ i, C870.adjugate i i ≠ 0) := by
  intro h
  have := certificate870
  rw [h.1] at this
  norm_num at this
def C871 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 0, 1, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate871 : C871.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction871 : ¬ (C871.det = 0 ∧ ∀ i, C871.adjugate i i ≠ 0) := by
  intro h
  have := certificate871
  rw [h.1] at this
  norm_num at this
def C872 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate872 : C872.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction872 : ¬ (C872.det = 0 ∧ ∀ i, C872.adjugate i i ≠ 0) := by
  intro h
  have := certificate872
  rw [h.1] at this
  norm_num at this
def C873 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate873 : C873.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction873 : ¬ (C873.det = 0 ∧ ∀ i, C873.adjugate i i ≠ 0) := by
  intro h
  have := certificate873
  rw [h.1] at this
  norm_num at this
def C874 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate874 : C874.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction874 : ¬ (C874.det = 0 ∧ ∀ i, C874.adjugate i i ≠ 0) := by
  intro h
  have := certificate874
  rw [h.1] at this
  norm_num at this
def C875 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate875 : C875.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction875 : ¬ (C875.det = 0 ∧ ∀ i, C875.adjugate i i ≠ 0) := by
  intro h
  have := certificate875
  rw [h.1] at this
  norm_num at this
def C876 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate876 : C876.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction876 : ¬ (C876.det = 0 ∧ ∀ i, C876.adjugate i i ≠ 0) := by
  intro h
  have := certificate876
  rw [h.1] at this
  norm_num at this
def C877 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate877 : C877.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction877 : ¬ (C877.det = 0 ∧ ∀ i, C877.adjugate i i ≠ 0) := by
  intro h
  have := certificate877
  rw [h.1] at this
  norm_num at this
def C878 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate878 : C878.det = (16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction878 : ¬ (C878.det = 0 ∧ ∀ i, C878.adjugate i i ≠ 0) := by
  intro h
  have := certificate878
  rw [h.1] at this
  norm_num at this
def C879 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate879 : C879.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction879 : ¬ (C879.det = 0 ∧ ∀ i, C879.adjugate i i ≠ 0) := by
  intro h
  have := certificate879
  rw [h.1] at this
  norm_num at this
def C880 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate880 : C880.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction880 : ¬ (C880.det = 0 ∧ ∀ i, C880.adjugate i i ≠ 0) := by
  intro h
  have := certificate880
  rw [h.1] at this
  norm_num at this
def C881 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate881 : C881.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction881 : ¬ (C881.det = 0 ∧ ∀ i, C881.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate881
def C882 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate882 : C882.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction882 : ¬ (C882.det = 0 ∧ ∀ i, C882.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate882
def C883 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate883 : C883.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction883 : ¬ (C883.det = 0 ∧ ∀ i, C883.adjugate i i ≠ 0) := by
  intro h
  have := certificate883
  rw [h.1] at this
  norm_num at this
def C884 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate884 : C884.det = (-32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction884 : ¬ (C884.det = 0 ∧ ∀ i, C884.adjugate i i ≠ 0) := by
  intro h
  have := certificate884
  rw [h.1] at this
  norm_num at this
def C885 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate885 : C885.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction885 : ¬ (C885.det = 0 ∧ ∀ i, C885.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate885
def C886 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate886 : C886.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction886 : ¬ (C886.det = 0 ∧ ∀ i, C886.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate886
def C887 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 0, 1, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate887 : C887.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction887 : ¬ (C887.det = 0 ∧ ∀ i, C887.adjugate i i ≠ 0) := by
  intro h
  have := certificate887
  rw [h.1] at this
  norm_num at this
def C888 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate888 : C888.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction888 : ¬ (C888.det = 0 ∧ ∀ i, C888.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate888
def C889 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate889 : C889.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction889 : ¬ (C889.det = 0 ∧ ∀ i, C889.adjugate i i ≠ 0) := by
  intro h
  have := certificate889
  rw [h.1] at this
  norm_num at this
def C890 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate890 : C890.adjugate 5 5 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction890 : ¬ (C890.det = 0 ∧ ∀ i, C890.adjugate i i ≠ 0) := by
  intro h
  exact h.2 5 certificate890
def C891 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate891 : C891.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction891 : ¬ (C891.det = 0 ∧ ∀ i, C891.adjugate i i ≠ 0) := by
  intro h
  have := certificate891
  rw [h.1] at this
  norm_num at this
def C892 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate892 : C892.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction892 : ¬ (C892.det = 0 ∧ ∀ i, C892.adjugate i i ≠ 0) := by
  intro h
  have := certificate892
  rw [h.1] at this
  norm_num at this
def C893 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, 2]
theorem certificate893 : C893.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction893 : ¬ (C893.det = 0 ∧ ∀ i, C893.adjugate i i ≠ 0) := by
  intro h
  have := certificate893
  rw [h.1] at this
  norm_num at this
def C894 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate894 : C894.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction894 : ¬ (C894.det = 0 ∧ ∀ i, C894.adjugate i i ≠ 0) := by
  intro h
  have := certificate894
  rw [h.1] at this
  norm_num at this
def C895 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, -1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, -1, 1; 0, 0, 0, 0, 0, 0, 1, -2]
theorem certificate895 : C895.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction895 : ¬ (C895.det = 0 ∧ ∀ i, C895.adjugate i i ≠ 0) := by
  intro h
  have := certificate895
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0027
