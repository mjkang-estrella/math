import SupportData124
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport124
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0188.C6036, NewCertificates0188.C6037, NewCertificates0188.C6038, NewCertificates0188.C6039, NewCertificates0188.C6040, NewCertificates0188.C6041, NewCertificates0188.C6042, NewCertificates0188.C6043, NewCertificates0188.C6044, NewCertificates0188.C6045, NewCertificates0188.C6046, NewCertificates0188.C6047, NewCertificates0189.C6048, NewCertificates0189.C6049, NewCertificates0189.C6050, NewCertificates0189.C6051} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0188.obstruction6036
  · exact NewCertificates0188.obstruction6037
  · exact NewCertificates0188.obstruction6038
  · exact NewCertificates0188.obstruction6039
  · exact NewCertificates0188.obstruction6040
  · exact NewCertificates0188.obstruction6041
  · exact NewCertificates0188.obstruction6042
  · exact NewCertificates0188.obstruction6043
  · exact NewCertificates0188.obstruction6044
  · exact NewCertificates0188.obstruction6045
  · exact NewCertificates0188.obstruction6046
  · exact NewCertificates0188.obstruction6047
  · exact NewCertificates0189.obstruction6048
  · exact NewCertificates0189.obstruction6049
  · exact NewCertificates0189.obstruction6050
  · exact NewCertificates0189.obstruction6051
end Nut8.FiniteSupport124
