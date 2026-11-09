import VerifiedDet
namespace Nut8.NewCertificates0179
def C5728 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1]
theorem certificate5728 : C5728.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5728 : ¬ (C5728.det = 0 ∧ ∀ i, C5728.adjugate i i ≠ 0) := by
  intro h
  have := certificate5728
  rw [h.1] at this
  norm_num at this
def C5729 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 1, 0, -1]
theorem certificate5729 : C5729.det = (-3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5729 : ¬ (C5729.det = 0 ∧ ∀ i, C5729.adjugate i i ≠ 0) := by
  intro h
  have := certificate5729
  rw [h.1] at this
  norm_num at this
def C5730 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -1, 0, 1]
theorem certificate5730 : C5730.det = (1 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5730 : ¬ (C5730.det = 0 ∧ ∀ i, C5730.adjugate i i ≠ 0) := by
  intro h
  have := certificate5730
  rw [h.1] at this
  norm_num at this
def C5731 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -1, 0, -1]
theorem certificate5731 : C5731.det = (-7 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5731 : ¬ (C5731.det = 0 ∧ ∀ i, C5731.adjugate i i ≠ 0) := by
  intro h
  have := certificate5731
  rw [h.1] at this
  norm_num at this
def C5732 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5732 : C5732.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5732 : ¬ (C5732.det = 0 ∧ ∀ i, C5732.adjugate i i ≠ 0) := by
  intro h
  have := certificate5732
  rw [h.1] at this
  norm_num at this
def C5733 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5733 : C5733.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5733 : ¬ (C5733.det = 0 ∧ ∀ i, C5733.adjugate i i ≠ 0) := by
  intro h
  have := certificate5733
  rw [h.1] at this
  norm_num at this
def C5734 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5734 : C5734.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5734 : ¬ (C5734.det = 0 ∧ ∀ i, C5734.adjugate i i ≠ 0) := by
  intro h
  have := certificate5734
  rw [h.1] at this
  norm_num at this
def C5735 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5735 : C5735.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5735 : ¬ (C5735.det = 0 ∧ ∀ i, C5735.adjugate i i ≠ 0) := by
  intro h
  have := certificate5735
  rw [h.1] at this
  norm_num at this
def C5736 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5736 : C5736.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5736 : ¬ (C5736.det = 0 ∧ ∀ i, C5736.adjugate i i ≠ 0) := by
  intro h
  have := certificate5736
  rw [h.1] at this
  norm_num at this
def C5737 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5737 : C5737.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5737 : ¬ (C5737.det = 0 ∧ ∀ i, C5737.adjugate i i ≠ 0) := by
  intro h
  have := certificate5737
  rw [h.1] at this
  norm_num at this
def C5738 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, -1, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, -1, 0, 1, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5738 : C5738.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5738 : ¬ (C5738.det = 0 ∧ ∀ i, C5738.adjugate i i ≠ 0) := by
  intro h
  have := certificate5738
  rw [h.1] at this
  norm_num at this
def C5739 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, -1, 0, -1, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, -1, 0, -1, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5739 : C5739.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5739 : ¬ (C5739.det = 0 ∧ ∀ i, C5739.adjugate i i ≠ 0) := by
  intro h
  have := certificate5739
  rw [h.1] at this
  norm_num at this
def C5740 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1]
theorem certificate5740 : C5740.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5740 : ¬ (C5740.det = 0 ∧ ∀ i, C5740.adjugate i i ≠ 0) := by
  intro h
  have := certificate5740
  rw [h.1] at this
  norm_num at this
def C5741 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, -1]
theorem certificate5741 : C5741.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5741 : ¬ (C5741.det = 0 ∧ ∀ i, C5741.adjugate i i ≠ 0) := by
  intro h
  have := certificate5741
  rw [h.1] at this
  norm_num at this
def C5742 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1]
theorem certificate5742 : C5742.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5742 : ¬ (C5742.det = 0 ∧ ∀ i, C5742.adjugate i i ≠ 0) := by
  intro h
  have := certificate5742
  rw [h.1] at this
  norm_num at this
def C5743 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, -1]
theorem certificate5743 : C5743.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5743 : ¬ (C5743.det = 0 ∧ ∀ i, C5743.adjugate i i ≠ 0) := by
  intro h
  have := certificate5743
  rw [h.1] at this
  norm_num at this
def C5744 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1]
theorem certificate5744 : C5744.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5744 : ¬ (C5744.det = 0 ∧ ∀ i, C5744.adjugate i i ≠ 0) := by
  intro h
  have := certificate5744
  rw [h.1] at this
  norm_num at this
def C5745 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, -1]
theorem certificate5745 : C5745.det = (3 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5745 : ¬ (C5745.det = 0 ∧ ∀ i, C5745.adjugate i i ≠ 0) := by
  intro h
  have := certificate5745
  rw [h.1] at this
  norm_num at this
def C5746 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, 1]
theorem certificate5746 : C5746.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5746 : ¬ (C5746.det = 0 ∧ ∀ i, C5746.adjugate i i ≠ 0) := by
  intro h
  have := certificate5746
  rw [h.1] at this
  norm_num at this
def C5747 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -1, 0, -1]
theorem certificate5747 : C5747.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5747 : ¬ (C5747.det = 0 ∧ ∀ i, C5747.adjugate i i ≠ 0) := by
  intro h
  have := certificate5747
  rw [h.1] at this
  norm_num at this
def C5748 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5748 : C5748.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5748 : ¬ (C5748.det = 0 ∧ ∀ i, C5748.adjugate i i ≠ 0) := by
  intro h
  have := certificate5748
  rw [h.1] at this
  norm_num at this
def C5749 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5749 : C5749.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5749 : ¬ (C5749.det = 0 ∧ ∀ i, C5749.adjugate i i ≠ 0) := by
  intro h
  have := certificate5749
  rw [h.1] at this
  norm_num at this
def C5750 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5750 : C5750.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5750 : ¬ (C5750.det = 0 ∧ ∀ i, C5750.adjugate i i ≠ 0) := by
  intro h
  have := certificate5750
  rw [h.1] at this
  norm_num at this
def C5751 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5751 : C5751.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5751 : ¬ (C5751.det = 0 ∧ ∀ i, C5751.adjugate i i ≠ 0) := by
  intro h
  have := certificate5751
  rw [h.1] at this
  norm_num at this
def C5752 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5752 : C5752.det = (40 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5752 : ¬ (C5752.det = 0 ∧ ∀ i, C5752.adjugate i i ≠ 0) := by
  intro h
  have := certificate5752
  rw [h.1] at this
  norm_num at this
def C5753 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, 2, 0, 0]
theorem certificate5753 : C5753.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5753 : ¬ (C5753.det = 0 ∧ ∀ i, C5753.adjugate i i ≠ 0) := by
  intro h
  have := certificate5753
  rw [h.1] at this
  norm_num at this
def C5754 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5754 : C5754.det = (24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5754 : ¬ (C5754.det = 0 ∧ ∀ i, C5754.adjugate i i ≠ 0) := by
  intro h
  have := certificate5754
  rw [h.1] at this
  norm_num at this
def C5755 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, -1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, -2, 0; 0, 0, 1, 0, 0, 0, 0, -2; 0, 0, 1, 0, -2, 0, 0, 0; 0, 0, 0, 1, 0, -2, 0, 0]
theorem certificate5755 : C5755.det = (-24 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5755 : ¬ (C5755.det = 0 ∧ ∀ i, C5755.adjugate i i ≠ 0) := by
  intro h
  have := certificate5755
  rw [h.1] at this
  norm_num at this
def C5756 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5756 : C5756.det = (-21 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5756 : ¬ (C5756.det = 0 ∧ ∀ i, C5756.adjugate i i ≠ 0) := by
  intro h
  have := certificate5756
  rw [h.1] at this
  norm_num at this
def C5757 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, 1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 2, 0, 1, 0, 0]
theorem certificate5757 : C5757.det = (-13 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5757 : ¬ (C5757.det = 0 ∧ ∀ i, C5757.adjugate i i ≠ 0) := by
  intro h
  have := certificate5757
  rw [h.1] at this
  norm_num at this
def C5758 : Matrix (Fin 8) (Fin 8) ℤ := !![1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, -1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5758 : C5758.det = (-29 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5758 : ¬ (C5758.det = 0 ∧ ∀ i, C5758.adjugate i i ≠ 0) := by
  intro h
  have := certificate5758
  rw [h.1] at this
  norm_num at this
def C5759 : Matrix (Fin 8) (Fin 8) ℤ := !![-1, 1, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, -1, 0, 1, 0; 0, 0, 1, 0, 0, -1, 0, -1; 0, 0, 1, 0, 1, 0, -1, 0; 0, 0, 0, 2, 0, -1, 0, 0]
theorem certificate5759 : C5759.det = (-5 : ℤ) := by
  rw [← sparseDet_eq_det]
  decide +kernel
theorem obstruction5759 : ¬ (C5759.det = 0 ∧ ∀ i, C5759.adjugate i i ≠ 0) := by
  intro h
  have := certificate5759
  rw [h.1] at this
  norm_num at this
end Nut8.NewCertificates0179
