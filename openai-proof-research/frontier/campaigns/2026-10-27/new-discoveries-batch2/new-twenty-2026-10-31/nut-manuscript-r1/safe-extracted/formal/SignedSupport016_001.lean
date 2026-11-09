import SupportData016
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport016
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0025.C816, NewCertificates0025.C817, NewCertificates0025.C818, NewCertificates0025.C819, NewCertificates0025.C820, NewCertificates0025.C821, NewCertificates0025.C822, NewCertificates0025.C823} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0025.obstruction816
  · exact NewCertificates0025.obstruction817
  · exact NewCertificates0025.obstruction818
  · exact NewCertificates0025.obstruction819
  · exact NewCertificates0025.obstruction820
  · exact NewCertificates0025.obstruction821
  · exact NewCertificates0025.obstruction822
  · exact NewCertificates0025.obstruction823
end Nut8.FiniteSupport016
