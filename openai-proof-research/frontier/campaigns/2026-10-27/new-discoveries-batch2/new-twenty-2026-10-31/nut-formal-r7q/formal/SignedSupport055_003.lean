import SupportData055
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport055
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0084.C2698, NewCertificates0084.C2699, NewCertificates0084.C2700, NewCertificates0084.C2701} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0084.obstruction2698
  · exact NewCertificates0084.obstruction2699
  · exact NewCertificates0084.obstruction2700
  · exact NewCertificates0084.obstruction2701
end Nut8.FiniteSupport055
