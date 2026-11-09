import SupportData108
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport108
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0157.C5030, NewCertificates0157.C5031, NewCertificates0157.C5032, NewCertificates0157.C5033, NewCertificates0157.C5034, NewCertificates0157.C5035, NewCertificates0157.C5036, NewCertificates0157.C5037} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0157.C5038, NewCertificates0157.C5039, NewCertificates0157.C5040, NewCertificates0157.C5041, NewCertificates0157.C5042, NewCertificates0157.C5043, NewCertificates0157.C5044, NewCertificates0157.C5045} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0157.C5046, NewCertificates0157.C5047, NewCertificates0157.C5048, NewCertificates0157.C5049, NewCertificates0157.C5050, NewCertificates0157.C5051, NewCertificates0157.C5052, NewCertificates0157.C5053} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0157.C5054, NewCertificates0157.C5055, NewCertificates0158.C5056, NewCertificates0158.C5057, NewCertificates0158.C5058, NewCertificates0158.C5059, NewCertificates0158.C5060, NewCertificates0158.C5061} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0157.obstruction5030
  · exact NewCertificates0157.obstruction5031
  · exact NewCertificates0157.obstruction5032
  · exact NewCertificates0157.obstruction5033
  · exact NewCertificates0157.obstruction5034
  · exact NewCertificates0157.obstruction5035
  · exact NewCertificates0157.obstruction5036
  · exact NewCertificates0157.obstruction5037
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0157.obstruction5038
  · exact NewCertificates0157.obstruction5039
  · exact NewCertificates0157.obstruction5040
  · exact NewCertificates0157.obstruction5041
  · exact NewCertificates0157.obstruction5042
  · exact NewCertificates0157.obstruction5043
  · exact NewCertificates0157.obstruction5044
  · exact NewCertificates0157.obstruction5045
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0157.obstruction5046
  · exact NewCertificates0157.obstruction5047
  · exact NewCertificates0157.obstruction5048
  · exact NewCertificates0157.obstruction5049
  · exact NewCertificates0157.obstruction5050
  · exact NewCertificates0157.obstruction5051
  · exact NewCertificates0157.obstruction5052
  · exact NewCertificates0157.obstruction5053
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0157.obstruction5054
  · exact NewCertificates0157.obstruction5055
  · exact NewCertificates0158.obstruction5056
  · exact NewCertificates0158.obstruction5057
  · exact NewCertificates0158.obstruction5058
  · exact NewCertificates0158.obstruction5059
  · exact NewCertificates0158.obstruction5060
  · exact NewCertificates0158.obstruction5061
end Nut8.FiniteSupport108
