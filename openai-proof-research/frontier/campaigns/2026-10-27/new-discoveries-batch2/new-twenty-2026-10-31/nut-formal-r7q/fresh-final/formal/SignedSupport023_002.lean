import SupportData023
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport023
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0035.C1148, NewCertificates0035.C1149, NewCertificates0035.C1150, NewCertificates0035.C1151, NewCertificates0036.C1152, NewCertificates0036.C1153, NewCertificates0036.C1154, NewCertificates0036.C1155} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0035.obstruction1148
  · exact NewCertificates0035.obstruction1149
  · exact NewCertificates0035.obstruction1150
  · exact NewCertificates0035.obstruction1151
  · exact NewCertificates0036.obstruction1152
  · exact NewCertificates0036.obstruction1153
  · exact NewCertificates0036.obstruction1154
  · exact NewCertificates0036.obstruction1155
end Nut8.FiniteSupport023
