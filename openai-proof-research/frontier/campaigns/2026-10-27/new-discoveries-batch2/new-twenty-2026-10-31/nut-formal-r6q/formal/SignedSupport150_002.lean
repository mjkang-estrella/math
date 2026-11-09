import SupportData150
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport150
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0220.C7060, NewCertificates0220.C7061, NewCertificates0220.C7062, NewCertificates0220.C7063, NewCertificates0220.C7064, NewCertificates0220.C7065, NewCertificates0220.C7066, NewCertificates0220.C7067} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0220.obstruction7060
  · exact NewCertificates0220.obstruction7061
  · exact NewCertificates0220.obstruction7062
  · exact NewCertificates0220.obstruction7063
  · exact NewCertificates0220.obstruction7064
  · exact NewCertificates0220.obstruction7065
  · exact NewCertificates0220.obstruction7066
  · exact NewCertificates0220.obstruction7067
end Nut8.FiniteSupport150
