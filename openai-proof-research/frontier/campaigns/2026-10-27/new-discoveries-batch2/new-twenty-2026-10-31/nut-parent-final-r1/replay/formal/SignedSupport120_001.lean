import SupportData120
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport120
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0179.C5756, NewCertificates0179.C5757, NewCertificates0179.C5758, NewCertificates0179.C5759, NewCertificates0180.C5760, NewCertificates0180.C5761, NewCertificates0180.C5762, NewCertificates0180.C5763} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0180.C5764, NewCertificates0180.C5765, NewCertificates0180.C5766, NewCertificates0180.C5767, NewCertificates0180.C5768, NewCertificates0180.C5769, NewCertificates0180.C5770, NewCertificates0180.C5771} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0179.obstruction5756
  · exact NewCertificates0179.obstruction5757
  · exact NewCertificates0179.obstruction5758
  · exact NewCertificates0179.obstruction5759
  · exact NewCertificates0180.obstruction5760
  · exact NewCertificates0180.obstruction5761
  · exact NewCertificates0180.obstruction5762
  · exact NewCertificates0180.obstruction5763
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0180.obstruction5764
  · exact NewCertificates0180.obstruction5765
  · exact NewCertificates0180.obstruction5766
  · exact NewCertificates0180.obstruction5767
  · exact NewCertificates0180.obstruction5768
  · exact NewCertificates0180.obstruction5769
  · exact NewCertificates0180.obstruction5770
  · exact NewCertificates0180.obstruction5771
end Nut8.FiniteSupport120
