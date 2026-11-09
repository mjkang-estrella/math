import SupportData153
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport153
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0225.C7200, NewCertificates0225.C7201, NewCertificates0225.C7202, NewCertificates0225.C7203, NewCertificates0225.C7204, NewCertificates0225.C7205, NewCertificates0225.C7206, NewCertificates0225.C7207} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0225.C7208, NewCertificates0225.C7209, NewCertificates0225.C7210, NewCertificates0225.C7211, NewCertificates0225.C7212, NewCertificates0225.C7213, NewCertificates0225.C7214, NewCertificates0225.C7215} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0225.C7216, NewCertificates0225.C7217, NewCertificates0225.C7218, NewCertificates0225.C7219, NewCertificates0225.C7220, NewCertificates0225.C7221, NewCertificates0225.C7222, NewCertificates0225.C7223} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0225.C7224, NewCertificates0225.C7225, NewCertificates0225.C7226, NewCertificates0225.C7227, NewCertificates0225.C7228, NewCertificates0225.C7229, NewCertificates0225.C7230, NewCertificates0225.C7231} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0225.obstruction7200
  · exact NewCertificates0225.obstruction7201
  · exact NewCertificates0225.obstruction7202
  · exact NewCertificates0225.obstruction7203
  · exact NewCertificates0225.obstruction7204
  · exact NewCertificates0225.obstruction7205
  · exact NewCertificates0225.obstruction7206
  · exact NewCertificates0225.obstruction7207
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0225.obstruction7208
  · exact NewCertificates0225.obstruction7209
  · exact NewCertificates0225.obstruction7210
  · exact NewCertificates0225.obstruction7211
  · exact NewCertificates0225.obstruction7212
  · exact NewCertificates0225.obstruction7213
  · exact NewCertificates0225.obstruction7214
  · exact NewCertificates0225.obstruction7215
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0225.obstruction7216
  · exact NewCertificates0225.obstruction7217
  · exact NewCertificates0225.obstruction7218
  · exact NewCertificates0225.obstruction7219
  · exact NewCertificates0225.obstruction7220
  · exact NewCertificates0225.obstruction7221
  · exact NewCertificates0225.obstruction7222
  · exact NewCertificates0225.obstruction7223
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0225.obstruction7224
  · exact NewCertificates0225.obstruction7225
  · exact NewCertificates0225.obstruction7226
  · exact NewCertificates0225.obstruction7227
  · exact NewCertificates0225.obstruction7228
  · exact NewCertificates0225.obstruction7229
  · exact NewCertificates0225.obstruction7230
  · exact NewCertificates0225.obstruction7231
end Nut8.FiniteSupport153
