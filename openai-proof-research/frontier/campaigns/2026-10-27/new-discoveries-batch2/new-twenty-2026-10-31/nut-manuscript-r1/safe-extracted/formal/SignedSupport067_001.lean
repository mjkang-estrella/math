import SupportData067
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport067
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0098.C3166, NewCertificates0098.C3167, NewCertificates0099.C3168, NewCertificates0099.C3169, NewCertificates0099.C3170, NewCertificates0099.C3171, NewCertificates0099.C3172, NewCertificates0099.C3173} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0098.obstruction3166
  · exact NewCertificates0098.obstruction3167
  · exact NewCertificates0099.obstruction3168
  · exact NewCertificates0099.obstruction3169
  · exact NewCertificates0099.obstruction3170
  · exact NewCertificates0099.obstruction3171
  · exact NewCertificates0099.obstruction3172
  · exact NewCertificates0099.obstruction3173
end Nut8.FiniteSupport067
