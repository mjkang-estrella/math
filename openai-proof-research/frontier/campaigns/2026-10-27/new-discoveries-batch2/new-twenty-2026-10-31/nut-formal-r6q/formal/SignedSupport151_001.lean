import SupportData151
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport151
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0221.C7100, NewCertificates0221.C7101, NewCertificates0221.C7102, NewCertificates0221.C7103, NewCertificates0222.C7104, NewCertificates0222.C7105, NewCertificates0222.C7106, NewCertificates0222.C7107} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0222.C7108, NewCertificates0222.C7109, NewCertificates0222.C7110, NewCertificates0222.C7111, NewCertificates0222.C7112, NewCertificates0222.C7113, NewCertificates0222.C7114, NewCertificates0222.C7115} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0222.C7116, NewCertificates0222.C7117, NewCertificates0222.C7118, NewCertificates0222.C7119, NewCertificates0222.C7120, NewCertificates0222.C7121, NewCertificates0222.C7122, NewCertificates0222.C7123} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0222.C7124, NewCertificates0222.C7125, NewCertificates0222.C7126, NewCertificates0222.C7127, NewCertificates0222.C7128, NewCertificates0222.C7129, NewCertificates0222.C7130, NewCertificates0222.C7131} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0221.obstruction7100
  · exact NewCertificates0221.obstruction7101
  · exact NewCertificates0221.obstruction7102
  · exact NewCertificates0221.obstruction7103
  · exact NewCertificates0222.obstruction7104
  · exact NewCertificates0222.obstruction7105
  · exact NewCertificates0222.obstruction7106
  · exact NewCertificates0222.obstruction7107
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0222.obstruction7108
  · exact NewCertificates0222.obstruction7109
  · exact NewCertificates0222.obstruction7110
  · exact NewCertificates0222.obstruction7111
  · exact NewCertificates0222.obstruction7112
  · exact NewCertificates0222.obstruction7113
  · exact NewCertificates0222.obstruction7114
  · exact NewCertificates0222.obstruction7115
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0222.obstruction7116
  · exact NewCertificates0222.obstruction7117
  · exact NewCertificates0222.obstruction7118
  · exact NewCertificates0222.obstruction7119
  · exact NewCertificates0222.obstruction7120
  · exact NewCertificates0222.obstruction7121
  · exact NewCertificates0222.obstruction7122
  · exact NewCertificates0222.obstruction7123
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0222.obstruction7124
  · exact NewCertificates0222.obstruction7125
  · exact NewCertificates0222.obstruction7126
  · exact NewCertificates0222.obstruction7127
  · exact NewCertificates0222.obstruction7128
  · exact NewCertificates0222.obstruction7129
  · exact NewCertificates0222.obstruction7130
  · exact NewCertificates0222.obstruction7131
end Nut8.FiniteSupport151
