import VerifiedDet
namespace Nut8.NewCertificates0149
def C4768 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4768 : C4768.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4768 : ¬ (C4768.det = 0 ∧ ∀ i, C4768.adjugate i i ≠ 0) := by
  intro h
  have := certificate4768
  rw [h.1] at this
  norm_num at this
def C4769 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4769 : C4769.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4769 : ¬ (C4769.det = 0 ∧ ∀ i, C4769.adjugate i i ≠ 0) := by
  intro h
  have := certificate4769
  rw [h.1] at this
  norm_num at this
def C4770 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4770 : C4770.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4770 : ¬ (C4770.det = 0 ∧ ∀ i, C4770.adjugate i i ≠ 0) := by
  intro h
  have := certificate4770
  rw [h.1] at this
  norm_num at this
def C4771 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4771 : C4771.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4771 : ¬ (C4771.det = 0 ∧ ∀ i, C4771.adjugate i i ≠ 0) := by
  intro h
  have := certificate4771
  rw [h.1] at this
  norm_num at this
def C4772 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4772 : C4772.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4772 : ¬ (C4772.det = 0 ∧ ∀ i, C4772.adjugate i i ≠ 0) := by
  intro h
  have := certificate4772
  rw [h.1] at this
  norm_num at this
def C4773 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4773 : C4773.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4773 : ¬ (C4773.det = 0 ∧ ∀ i, C4773.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate4773
def C4774 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4774 : C4774.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4774 : ¬ (C4774.det = 0 ∧ ∀ i, C4774.adjugate i i ≠ 0) := by
  intro h
  have := certificate4774
  rw [h.1] at this
  norm_num at this
def C4775 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4775 : C4775.det = (-8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4775 : ¬ (C4775.det = 0 ∧ ∀ i, C4775.adjugate i i ≠ 0) := by
  intro h
  have := certificate4775
  rw [h.1] at this
  norm_num at this
def C4776 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4776 : C4776.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4776 : ¬ (C4776.det = 0 ∧ ∀ i, C4776.adjugate i i ≠ 0) := by
  intro h
  have := certificate4776
  rw [h.1] at this
  norm_num at this
def C4777 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4777 : C4777.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4777 : ¬ (C4777.det = 0 ∧ ∀ i, C4777.adjugate i i ≠ 0) := by
  intro h
  have := certificate4777
  rw [h.1] at this
  norm_num at this
def C4778 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4778 : C4778.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4778 : ¬ (C4778.det = 0 ∧ ∀ i, C4778.adjugate i i ≠ 0) := by
  intro h
  have := certificate4778
  rw [h.1] at this
  norm_num at this
def C4779 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4779 : C4779.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4779 : ¬ (C4779.det = 0 ∧ ∀ i, C4779.adjugate i i ≠ 0) := by
  intro h
  have := certificate4779
  rw [h.1] at this
  norm_num at this
def C4780 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4780 : C4780.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4780 : ¬ (C4780.det = 0 ∧ ∀ i, C4780.adjugate i i ≠ 0) := by
  intro h
  have := certificate4780
  rw [h.1] at this
  norm_num at this
def C4781 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4781 : C4781.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4781 : ¬ (C4781.det = 0 ∧ ∀ i, C4781.adjugate i i ≠ 0) := by
  intro h
  have := certificate4781
  rw [h.1] at this
  norm_num at this
def C4782 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4782 : C4782.det = (-16 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4782 : ¬ (C4782.det = 0 ∧ ∀ i, C4782.adjugate i i ≠ 0) := by
  intro h
  have := certificate4782
  rw [h.1] at this
  norm_num at this
def C4783 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4783 : C4783.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4783 : ¬ (C4783.det = 0 ∧ ∀ i, C4783.adjugate i i ≠ 0) := by
  intro h
  have := certificate4783
  rw [h.1] at this
  norm_num at this
def C4784 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4784 : C4784.det = (12 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4784 : ¬ (C4784.det = 0 ∧ ∀ i, C4784.adjugate i i ≠ 0) := by
  intro h
  have := certificate4784
  rw [h.1] at this
  norm_num at this
def C4785 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4785 : C4785.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4785 : ¬ (C4785.det = 0 ∧ ∀ i, C4785.adjugate i i ≠ 0) := by
  intro h
  have := certificate4785
  rw [h.1] at this
  norm_num at this
def C4786 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4786 : C4786.adjugate 2 2 = 0 := by
  rw [← sparseDet_principal]
  decide +kernel
theorem obstruction4786 : ¬ (C4786.det = 0 ∧ ∀ i, C4786.adjugate i i ≠ 0) := by
  intro h
  exact h.2 2 certificate4786
def C4787 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4787 : C4787.det = (8 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4787 : ¬ (C4787.det = 0 ∧ ∀ i, C4787.adjugate i i ≠ 0) := by
  intro h
  have := certificate4787
  rw [h.1] at this
  norm_num at this
def C4788 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4788 : C4788.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4788 : ¬ (C4788.det = 0 ∧ ∀ i, C4788.adjugate i i ≠ 0) := by
  intro h
  have := certificate4788
  rw [h.1] at this
  norm_num at this
def C4789 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, -1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, -1, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, -1; 0, 0, 0, 1, 0, -1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4789 : C4789.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4789 : ¬ (C4789.det = 0 ∧ ∀ i, C4789.adjugate i i ≠ 0) := by
  intro h
  have := certificate4789
  rw [h.1] at this
  norm_num at this
def C4790 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4790 : C4790.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4790 : ¬ (C4790.det = 0 ∧ ∀ i, C4790.adjugate i i ≠ 0) := by
  intro h
  have := certificate4790
  rw [h.1] at this
  norm_num at this
def C4791 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4791 : C4791.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4791 : ¬ (C4791.det = 0 ∧ ∀ i, C4791.adjugate i i ≠ 0) := by
  intro h
  have := certificate4791
  rw [h.1] at this
  norm_num at this
def C4792 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4792 : C4792.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4792 : ¬ (C4792.det = 0 ∧ ∀ i, C4792.adjugate i i ≠ 0) := by
  intro h
  have := certificate4792
  rw [h.1] at this
  norm_num at this
def C4793 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, 1, -1, 0]
theorem certificate4793 : C4793.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4793 : ¬ (C4793.det = 0 ∧ ∀ i, C4793.adjugate i i ≠ 0) := by
  intro h
  have := certificate4793
  rw [h.1] at this
  norm_num at this
def C4794 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4794 : C4794.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4794 : ¬ (C4794.det = 0 ∧ ∀ i, C4794.adjugate i i ≠ 0) := by
  intro h
  have := certificate4794
  rw [h.1] at this
  norm_num at this
def C4795 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, -1, 1, 0]
theorem certificate4795 : C4795.det = (28 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4795 : ¬ (C4795.det = 0 ∧ ∀ i, C4795.adjugate i i ≠ 0) := by
  intro h
  have := certificate4795
  rw [h.1] at this
  norm_num at this
def C4796 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4796 : C4796.det = (4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4796 : ¬ (C4796.det = 0 ∧ ∀ i, C4796.adjugate i i ≠ 0) := by
  intro h
  have := certificate4796
  rw [h.1] at this
  norm_num at this
def C4797 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 1, -1; 0, 0, 0, 1, 0, 1, 0, -1; 0, 0, 0, 0, 1, -1, -1, 0]
theorem certificate4797 : C4797.det = (-4 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4797 : ¬ (C4797.det = 0 ∧ ∀ i, C4797.adjugate i i ≠ 0) := by
  intro h
  have := certificate4797
  rw [h.1] at this
  norm_num at this
def C4798 : Matrix (Fin 8) (Fin 8) ℤ := !![2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4798 : C4798.det = (-36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4798 : ¬ (C4798.det = 0 ∧ ∀ i, C4798.adjugate i i ≠ 0) := by
  intro h
  have := certificate4798
  rw [h.1] at this
  norm_num at this
def C4799 : Matrix (Fin 8) (Fin 8) ℤ := !![-2, 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, -1, 1; 0, 0, 0, 1, 0, -1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0]
theorem certificate4799 : C4799.det = (36 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction4799 : ¬ (C4799.det = 0 ∧ ∀ i, C4799.adjugate i i ≠ 0) := by
  intro h
  have := certificate4799
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0149
