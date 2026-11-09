import SupportData173
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport173
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0251.C8060, NewCertificates0251.C8061, NewCertificates0251.C8062, NewCertificates0251.C8063, NewCertificates0252.C8064, NewCertificates0252.C8065, NewCertificates0252.C8066, NewCertificates0252.C8067} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0251.obstruction8060
  · exact NewCertificates0251.obstruction8061
  · exact NewCertificates0251.obstruction8062
  · exact NewCertificates0251.obstruction8063
  · exact NewCertificates0252.obstruction8064
  · exact NewCertificates0252.obstruction8065
  · exact NewCertificates0252.obstruction8066
  · exact NewCertificates0252.obstruction8067
end Nut8.FiniteSupport173
