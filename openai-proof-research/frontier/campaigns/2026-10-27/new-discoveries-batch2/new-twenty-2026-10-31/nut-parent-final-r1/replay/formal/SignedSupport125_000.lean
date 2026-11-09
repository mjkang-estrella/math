import SupportData125
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport125
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0189.C6052, NewCertificates0189.C6053, NewCertificates0189.C6054, NewCertificates0189.C6055, NewCertificates0189.C6056, NewCertificates0189.C6057, NewCertificates0189.C6058, NewCertificates0189.C6059, NewCertificates0189.C6060, NewCertificates0189.C6061, NewCertificates0189.C6062, NewCertificates0189.C6063, NewCertificates0189.C6064, NewCertificates0189.C6065, NewCertificates0189.C6066, NewCertificates0189.C6067} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0189.obstruction6052
  · exact NewCertificates0189.obstruction6053
  · exact NewCertificates0189.obstruction6054
  · exact NewCertificates0189.obstruction6055
  · exact NewCertificates0189.obstruction6056
  · exact NewCertificates0189.obstruction6057
  · exact NewCertificates0189.obstruction6058
  · exact NewCertificates0189.obstruction6059
  · exact NewCertificates0189.obstruction6060
  · exact NewCertificates0189.obstruction6061
  · exact NewCertificates0189.obstruction6062
  · exact NewCertificates0189.obstruction6063
  · exact NewCertificates0189.obstruction6064
  · exact NewCertificates0189.obstruction6065
  · exact NewCertificates0189.obstruction6066
  · exact NewCertificates0189.obstruction6067
end Nut8.FiniteSupport125
