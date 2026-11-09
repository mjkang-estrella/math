import SupportData151
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport151
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0222.C7132, NewCertificates0222.C7133, NewCertificates0222.C7134, NewCertificates0222.C7135, NewCertificates0223.C7136, NewCertificates0223.C7137, NewCertificates0223.C7138, NewCertificates0223.C7139} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0222.obstruction7132
  · exact NewCertificates0222.obstruction7133
  · exact NewCertificates0222.obstruction7134
  · exact NewCertificates0222.obstruction7135
  · exact NewCertificates0223.obstruction7136
  · exact NewCertificates0223.obstruction7137
  · exact NewCertificates0223.obstruction7138
  · exact NewCertificates0223.obstruction7139
end Nut8.FiniteSupport151
