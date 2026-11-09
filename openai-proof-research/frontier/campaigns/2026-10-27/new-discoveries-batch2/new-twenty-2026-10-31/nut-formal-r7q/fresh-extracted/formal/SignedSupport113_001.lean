import SupportData113
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport113
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0173.C5540, NewCertificates0173.C5541, NewCertificates0173.C5542, NewCertificates0173.C5543, NewCertificates0173.C5544, NewCertificates0173.C5545, NewCertificates0173.C5546, NewCertificates0173.C5547} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0173.obstruction5540
  · exact NewCertificates0173.obstruction5541
  · exact NewCertificates0173.obstruction5542
  · exact NewCertificates0173.obstruction5543
  · exact NewCertificates0173.obstruction5544
  · exact NewCertificates0173.obstruction5545
  · exact NewCertificates0173.obstruction5546
  · exact NewCertificates0173.obstruction5547
end Nut8.FiniteSupport113
