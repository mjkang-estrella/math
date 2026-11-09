import VerifiedDet
namespace Nut8.NewCertificates0271
def C8672 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8672 : C8672.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8672 : ¬ (C8672.det = 0 ∧ ∀ i, C8672.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8672
def C8673 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8673 : C8673.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8673 : ¬ (C8673.det = 0 ∧ ∀ i, C8673.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8673
def C8674 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8674 : C8674.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8674 : ¬ (C8674.det = 0 ∧ ∀ i, C8674.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8674
def C8675 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8675 : C8675.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8675 : ¬ (C8675.det = 0 ∧ ∀ i, C8675.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8675
def C8676 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8676 : C8676.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8676 : ¬ (C8676.det = 0 ∧ ∀ i, C8676.adjugate i i ≠ 0) := by
  intro h
  have := certificate8676
  rw [h.1] at this
  norm_num at this
def C8677 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8677 : C8677.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8677 : ¬ (C8677.det = 0 ∧ ∀ i, C8677.adjugate i i ≠ 0) := by
  intro h
  have := certificate8677
  rw [h.1] at this
  norm_num at this
def C8678 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8678 : C8678.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8678 : ¬ (C8678.det = 0 ∧ ∀ i, C8678.adjugate i i ≠ 0) := by
  intro h
  have := certificate8678
  rw [h.1] at this
  norm_num at this
def C8679 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8679 : C8679.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8679 : ¬ (C8679.det = 0 ∧ ∀ i, C8679.adjugate i i ≠ 0) := by
  intro h
  have := certificate8679
  rw [h.1] at this
  norm_num at this
def C8680 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8680 : C8680.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8680 : ¬ (C8680.det = 0 ∧ ∀ i, C8680.adjugate i i ≠ 0) := by
  intro h
  have := certificate8680
  rw [h.1] at this
  norm_num at this
def C8681 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8681 : C8681.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8681 : ¬ (C8681.det = 0 ∧ ∀ i, C8681.adjugate i i ≠ 0) := by
  intro h
  have := certificate8681
  rw [h.1] at this
  norm_num at this
def C8682 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8682 : C8682.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8682 : ¬ (C8682.det = 0 ∧ ∀ i, C8682.adjugate i i ≠ 0) := by
  intro h
  have := certificate8682
  rw [h.1] at this
  norm_num at this
def C8683 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, -1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8683 : C8683.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8683 : ¬ (C8683.det = 0 ∧ ∀ i, C8683.adjugate i i ≠ 0) := by
  intro h
  have := certificate8683
  rw [h.1] at this
  norm_num at this
def C8684 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8684 : C8684.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8684 : ¬ (C8684.det = 0 ∧ ∀ i, C8684.adjugate i i ≠ 0) := by
  intro h
  have := certificate8684
  rw [h.1] at this
  norm_num at this
def C8685 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8685 : C8685.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8685 : ¬ (C8685.det = 0 ∧ ∀ i, C8685.adjugate i i ≠ 0) := by
  intro h
  have := certificate8685
  rw [h.1] at this
  norm_num at this
def C8686 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8686 : C8686.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8686 : ¬ (C8686.det = 0 ∧ ∀ i, C8686.adjugate i i ≠ 0) := by
  intro h
  have := certificate8686
  rw [h.1] at this
  norm_num at this
def C8687 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8687 : C8687.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8687 : ¬ (C8687.det = 0 ∧ ∀ i, C8687.adjugate i i ≠ 0) := by
  intro h
  have := certificate8687
  rw [h.1] at this
  norm_num at this
def C8688 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8688 : C8688.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8688 : ¬ (C8688.det = 0 ∧ ∀ i, C8688.adjugate i i ≠ 0) := by
  intro h
  have := certificate8688
  rw [h.1] at this
  norm_num at this
def C8689 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8689 : C8689.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8689 : ¬ (C8689.det = 0 ∧ ∀ i, C8689.adjugate i i ≠ 0) := by
  intro h
  have := certificate8689
  rw [h.1] at this
  norm_num at this
def C8690 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8690 : C8690.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8690 : ¬ (C8690.det = 0 ∧ ∀ i, C8690.adjugate i i ≠ 0) := by
  intro h
  have := certificate8690
  rw [h.1] at this
  norm_num at this
def C8691 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, 1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8691 : C8691.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8691 : ¬ (C8691.det = 0 ∧ ∀ i, C8691.adjugate i i ≠ 0) := by
  intro h
  have := certificate8691
  rw [h.1] at this
  norm_num at this
def C8692 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8692 : C8692.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8692 : ¬ (C8692.det = 0 ∧ ∀ i, C8692.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8692
def C8693 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8693 : C8693.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8693 : ¬ (C8693.det = 0 ∧ ∀ i, C8693.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8693
def C8694 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8694 : C8694.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8694 : ¬ (C8694.det = 0 ∧ ∀ i, C8694.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8694
def C8695 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8695 : C8695.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8695 : ¬ (C8695.det = 0 ∧ ∀ i, C8695.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8695
def C8696 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8696 : C8696.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8696 : ¬ (C8696.det = 0 ∧ ∀ i, C8696.adjugate i i ≠ 0) := by
  intro h
  have := certificate8696
  rw [h.1] at this
  norm_num at this
def C8697 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8697 : C8697.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8697 : ¬ (C8697.det = 0 ∧ ∀ i, C8697.adjugate i i ≠ 0) := by
  intro h
  have := certificate8697
  rw [h.1] at this
  norm_num at this
def C8698 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8698 : C8698.det = (48 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8698 : ¬ (C8698.det = 0 ∧ ∀ i, C8698.adjugate i i ≠ 0) := by
  intro h
  have := certificate8698
  rw [h.1] at this
  norm_num at this
def C8699 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, -1, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, -1, -1, 0; 0, 0, 0, 1, -1, 0, 0, 1; 0, 0, 0, 1, -1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8699 : C8699.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction8699 : ¬ (C8699.det = 0 ∧ ∀ i, C8699.adjugate i i ≠ 0) := by
  intro h
  have := certificate8699
  rw [h.1] at this
  norm_num at this
def C8700 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate8700 : C8700.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8700 : ¬ (C8700.det = 0 ∧ ∀ i, C8700.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8700
def C8701 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate8701 : C8701.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8701 : ¬ (C8701.det = 0 ∧ ∀ i, C8701.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8701
def C8702 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate8702 : C8702.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8702 : ¬ (C8702.det = 0 ∧ ∀ i, C8702.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8702
def C8703 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 2, 0, 0, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 0, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate8703 : C8703.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction8703 : ¬ (C8703.det = 0 ∧ ∀ i, C8703.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate8703
end Nut8.NewCertificates0271
