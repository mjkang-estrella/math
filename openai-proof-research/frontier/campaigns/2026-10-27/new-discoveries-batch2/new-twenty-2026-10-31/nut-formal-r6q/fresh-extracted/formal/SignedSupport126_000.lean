import SupportData126
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport126
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0189.C6068, NewCertificates0189.C6069, NewCertificates0189.C6070, NewCertificates0189.C6071, NewCertificates0189.C6072, NewCertificates0189.C6073, NewCertificates0189.C6074, NewCertificates0189.C6075, NewCertificates0189.C6076, NewCertificates0189.C6077, NewCertificates0189.C6078, NewCertificates0189.C6079, NewCertificates0190.C6080, NewCertificates0190.C6081, NewCertificates0190.C6082, NewCertificates0190.C6083, NewCertificates0190.C6084, NewCertificates0190.C6085, NewCertificates0190.C6086, NewCertificates0190.C6087, NewCertificates0190.C6088, NewCertificates0190.C6089, NewCertificates0190.C6090, NewCertificates0190.C6091, NewCertificates0190.C6092, NewCertificates0190.C6093, NewCertificates0190.C6094, NewCertificates0190.C6095, NewCertificates0190.C6096, NewCertificates0190.C6097, NewCertificates0190.C6098, NewCertificates0190.C6099} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0189.obstruction6068
  · exact NewCertificates0189.obstruction6069
  · exact NewCertificates0189.obstruction6070
  · exact NewCertificates0189.obstruction6071
  · exact NewCertificates0189.obstruction6072
  · exact NewCertificates0189.obstruction6073
  · exact NewCertificates0189.obstruction6074
  · exact NewCertificates0189.obstruction6075
  · exact NewCertificates0189.obstruction6076
  · exact NewCertificates0189.obstruction6077
  · exact NewCertificates0189.obstruction6078
  · exact NewCertificates0189.obstruction6079
  · exact NewCertificates0190.obstruction6080
  · exact NewCertificates0190.obstruction6081
  · exact NewCertificates0190.obstruction6082
  · exact NewCertificates0190.obstruction6083
  · exact NewCertificates0190.obstruction6084
  · exact NewCertificates0190.obstruction6085
  · exact NewCertificates0190.obstruction6086
  · exact NewCertificates0190.obstruction6087
  · exact NewCertificates0190.obstruction6088
  · exact NewCertificates0190.obstruction6089
  · exact NewCertificates0190.obstruction6090
  · exact NewCertificates0190.obstruction6091
  · exact NewCertificates0190.obstruction6092
  · exact NewCertificates0190.obstruction6093
  · exact NewCertificates0190.obstruction6094
  · exact NewCertificates0190.obstruction6095
  · exact NewCertificates0190.obstruction6096
  · exact NewCertificates0190.obstruction6097
  · exact NewCertificates0190.obstruction6098
  · exact NewCertificates0190.obstruction6099
end Nut8.FiniteSupport126
