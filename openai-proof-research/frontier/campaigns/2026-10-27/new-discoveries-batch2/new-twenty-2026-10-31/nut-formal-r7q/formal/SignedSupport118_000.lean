import SupportData118
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport118
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0176.C5644, NewCertificates0176.C5645, NewCertificates0176.C5646, NewCertificates0176.C5647, NewCertificates0176.C5648, NewCertificates0176.C5649, NewCertificates0176.C5650, NewCertificates0176.C5651, NewCertificates0176.C5652, NewCertificates0176.C5653, NewCertificates0176.C5654, NewCertificates0176.C5655, NewCertificates0176.C5656, NewCertificates0176.C5657, NewCertificates0176.C5658, NewCertificates0176.C5659} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0176.C5660, NewCertificates0176.C5661, NewCertificates0176.C5662, NewCertificates0176.C5663, NewCertificates0177.C5664, NewCertificates0177.C5665, NewCertificates0177.C5666, NewCertificates0177.C5667, NewCertificates0177.C5668, NewCertificates0177.C5669, NewCertificates0177.C5670, NewCertificates0177.C5671, NewCertificates0177.C5672, NewCertificates0177.C5673, NewCertificates0177.C5674, NewCertificates0177.C5675} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0176.obstruction5644
  · exact NewCertificates0176.obstruction5645
  · exact NewCertificates0176.obstruction5646
  · exact NewCertificates0176.obstruction5647
  · exact NewCertificates0176.obstruction5648
  · exact NewCertificates0176.obstruction5649
  · exact NewCertificates0176.obstruction5650
  · exact NewCertificates0176.obstruction5651
  · exact NewCertificates0176.obstruction5652
  · exact NewCertificates0176.obstruction5653
  · exact NewCertificates0176.obstruction5654
  · exact NewCertificates0176.obstruction5655
  · exact NewCertificates0176.obstruction5656
  · exact NewCertificates0176.obstruction5657
  · exact NewCertificates0176.obstruction5658
  · exact NewCertificates0176.obstruction5659
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0176.obstruction5660
  · exact NewCertificates0176.obstruction5661
  · exact NewCertificates0176.obstruction5662
  · exact NewCertificates0176.obstruction5663
  · exact NewCertificates0177.obstruction5664
  · exact NewCertificates0177.obstruction5665
  · exact NewCertificates0177.obstruction5666
  · exact NewCertificates0177.obstruction5667
  · exact NewCertificates0177.obstruction5668
  · exact NewCertificates0177.obstruction5669
  · exact NewCertificates0177.obstruction5670
  · exact NewCertificates0177.obstruction5671
  · exact NewCertificates0177.obstruction5672
  · exact NewCertificates0177.obstruction5673
  · exact NewCertificates0177.obstruction5674
  · exact NewCertificates0177.obstruction5675
end Nut8.FiniteSupport118
