import SupportData152
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport152
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0224.C7172, NewCertificates0224.C7173, NewCertificates0224.C7174, NewCertificates0224.C7175, NewCertificates0224.C7176, NewCertificates0224.C7177, NewCertificates0224.C7178, NewCertificates0224.C7179} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0224.C7180, NewCertificates0224.C7181, NewCertificates0224.C7182, NewCertificates0224.C7183, NewCertificates0224.C7184, NewCertificates0224.C7185, NewCertificates0224.C7186, NewCertificates0224.C7187} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0224.C7188, NewCertificates0224.C7189, NewCertificates0224.C7190, NewCertificates0224.C7191, NewCertificates0224.C7192, NewCertificates0224.C7193, NewCertificates0224.C7194, NewCertificates0224.C7195} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0224.C7196, NewCertificates0224.C7197, NewCertificates0224.C7198, NewCertificates0224.C7199} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0224.obstruction7172
  · exact NewCertificates0224.obstruction7173
  · exact NewCertificates0224.obstruction7174
  · exact NewCertificates0224.obstruction7175
  · exact NewCertificates0224.obstruction7176
  · exact NewCertificates0224.obstruction7177
  · exact NewCertificates0224.obstruction7178
  · exact NewCertificates0224.obstruction7179
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0224.obstruction7180
  · exact NewCertificates0224.obstruction7181
  · exact NewCertificates0224.obstruction7182
  · exact NewCertificates0224.obstruction7183
  · exact NewCertificates0224.obstruction7184
  · exact NewCertificates0224.obstruction7185
  · exact NewCertificates0224.obstruction7186
  · exact NewCertificates0224.obstruction7187
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0224.obstruction7188
  · exact NewCertificates0224.obstruction7189
  · exact NewCertificates0224.obstruction7190
  · exact NewCertificates0224.obstruction7191
  · exact NewCertificates0224.obstruction7192
  · exact NewCertificates0224.obstruction7193
  · exact NewCertificates0224.obstruction7194
  · exact NewCertificates0224.obstruction7195
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0224.obstruction7196
  · exact NewCertificates0224.obstruction7197
  · exact NewCertificates0224.obstruction7198
  · exact NewCertificates0224.obstruction7199
end Nut8.FiniteSupport152
