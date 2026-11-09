import VerifiedDet
namespace Nut8.NewCertificates0177
def C5664 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5664 : C5664.det = (20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5664 : ¬ (C5664.det = 0 ∧ ∀ i, C5664.adjugate i i ≠ 0) := by
  intro h
  have := certificate5664
  rw [h.1] at this
  norm_num at this
def C5665 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5665 : C5665.det = (-28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5665 : ¬ (C5665.det = 0 ∧ ∀ i, C5665.adjugate i i ≠ 0) := by
  intro h
  have := certificate5665
  rw [h.1] at this
  norm_num at this
def C5666 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5666 : C5666.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5666 : ¬ (C5666.det = 0 ∧ ∀ i, C5666.adjugate i i ≠ 0) := by
  intro h
  have := certificate5666
  rw [h.1] at this
  norm_num at this
def C5667 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 1, 1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5667 : C5667.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5667 : ¬ (C5667.det = 0 ∧ ∀ i, C5667.adjugate i i ≠ 0) := by
  intro h
  have := certificate5667
  rw [h.1] at this
  norm_num at this
def C5668 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5668 : C5668.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5668 : ¬ (C5668.det = 0 ∧ ∀ i, C5668.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5668
def C5669 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5669 : C5669.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5669 : ¬ (C5669.det = 0 ∧ ∀ i, C5669.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate5669
def C5670 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5670 : C5670.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5670 : ¬ (C5670.det = 0 ∧ ∀ i, C5670.adjugate i i ≠ 0) := by
  intro h
  have := certificate5670
  rw [h.1] at this
  norm_num at this
def C5671 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5671 : C5671.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5671 : ¬ (C5671.det = 0 ∧ ∀ i, C5671.adjugate i i ≠ 0) := by
  intro h
  have := certificate5671
  rw [h.1] at this
  norm_num at this
def C5672 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5672 : C5672.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5672 : ¬ (C5672.det = 0 ∧ ∀ i, C5672.adjugate i i ≠ 0) := by
  intro h
  have := certificate5672
  rw [h.1] at this
  norm_num at this
def C5673 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5673 : C5673.det = (32 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5673 : ¬ (C5673.det = 0 ∧ ∀ i, C5673.adjugate i i ≠ 0) := by
  intro h
  have := certificate5673
  rw [h.1] at this
  norm_num at this
def C5674 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5674 : C5674.adjugate 3 3 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5674 : ¬ (C5674.det = 0 ∧ ∀ i, C5674.adjugate i i ≠ 0) := by
  intro h
  exact h.2 3 certificate5674
def C5675 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, -1, 0, 1, 0, 0; 0, 1, -1, -1, 0, 0, 0, 0; 0, 1, 0, 0, 0, -1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5675 : C5675.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5675 : ¬ (C5675.det = 0 ∧ ∀ i, C5675.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5675
def C5676 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5676 : C5676.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5676 : ¬ (C5676.det = 0 ∧ ∀ i, C5676.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5676
def C5677 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5677 : C5677.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5677 : ¬ (C5677.det = 0 ∧ ∀ i, C5677.adjugate i i ≠ 0) := by
  intro h
  have := certificate5677
  rw [h.1] at this
  norm_num at this
def C5678 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5678 : C5678.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5678 : ¬ (C5678.det = 0 ∧ ∀ i, C5678.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5678
def C5679 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5679 : C5679.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5679 : ¬ (C5679.det = 0 ∧ ∀ i, C5679.adjugate i i ≠ 0) := by
  intro h
  have := certificate5679
  rw [h.1] at this
  norm_num at this
def C5680 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1]
theorem certificate5680 : C5680.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5680 : ¬ (C5680.det = 0 ∧ ∀ i, C5680.adjugate i i ≠ 0) := by
  intro h
  have := certificate5680
  rw [h.1] at this
  norm_num at this
def C5681 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 1, 1, -1]
theorem certificate5681 : C5681.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5681 : ¬ (C5681.det = 0 ∧ ∀ i, C5681.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5681
def C5682 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 1, -1, 1]
theorem certificate5682 : C5682.det = (-12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5682 : ¬ (C5682.det = 0 ∧ ∀ i, C5682.adjugate i i ≠ 0) := by
  intro h
  have := certificate5682
  rw [h.1] at this
  norm_num at this
def C5683 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 1, -1, -1]
theorem certificate5683 : C5683.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5683 : ¬ (C5683.det = 0 ∧ ∀ i, C5683.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5683
def C5684 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5684 : C5684.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5684 : ¬ (C5684.det = 0 ∧ ∀ i, C5684.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5684
def C5685 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5685 : C5685.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5685 : ¬ (C5685.det = 0 ∧ ∀ i, C5685.adjugate i i ≠ 0) := by
  intro h
  have := certificate5685
  rw [h.1] at this
  norm_num at this
def C5686 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5686 : C5686.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5686 : ¬ (C5686.det = 0 ∧ ∀ i, C5686.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5686
def C5687 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5687 : C5687.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5687 : ¬ (C5687.det = 0 ∧ ∀ i, C5687.adjugate i i ≠ 0) := by
  intro h
  have := certificate5687
  rw [h.1] at this
  norm_num at this
def C5688 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5688 : C5688.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5688 : ¬ (C5688.det = 0 ∧ ∀ i, C5688.adjugate i i ≠ 0) := by
  intro h
  have := certificate5688
  rw [h.1] at this
  norm_num at this
def C5689 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 2, 0]
theorem certificate5689 : C5689.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5689 : ¬ (C5689.det = 0 ∧ ∀ i, C5689.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5689
def C5690 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5690 : C5690.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5690 : ¬ (C5690.det = 0 ∧ ∀ i, C5690.adjugate i i ≠ 0) := by
  intro h
  have := certificate5690
  rw [h.1] at this
  norm_num at this
def C5691 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 1, 0, -1, -1, 0, 0, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 0, 0, 0, 1, -2, 0]
theorem certificate5691 : C5691.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5691 : ¬ (C5691.det = 0 ∧ ∀ i, C5691.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5691
def C5692 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5692 : C5692.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5692 : ¬ (C5692.det = 0 ∧ ∀ i, C5692.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5692
def C5693 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, 1; 0, 0, 0, 0, 0, 2, 1, 0]
theorem certificate5693 : C5693.det = (-20 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5693 : ¬ (C5693.det = 0 ∧ ∀ i, C5693.adjugate i i ≠ 0) := by
  intro h
  have := certificate5693
  rw [h.1] at this
  norm_num at this
def C5694 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5694 : C5694.adjugate 0 0 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction5694 : ¬ (C5694.det = 0 ∧ ∀ i, C5694.adjugate i i ≠ 0) := by
  intro h
  exact h.2 0 certificate5694
def C5695 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 1, 0, 0, 0; 0, 1, 0, 1, -1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, -1, -1; 0, 0, 0, 0, 0, 2, -1, 0]
theorem certificate5695 : C5695.det = (-52 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5695 : ¬ (C5695.det = 0 ∧ ∀ i, C5695.adjugate i i ≠ 0) := by
  intro h
  have := certificate5695
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0177
