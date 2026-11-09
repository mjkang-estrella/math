import SupportData154
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport154
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0226.C7260, NewCertificates0226.C7261, NewCertificates0226.C7262, NewCertificates0226.C7263, NewCertificates0227.C7264, NewCertificates0227.C7265, NewCertificates0227.C7266, NewCertificates0227.C7267} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0227.C7268, NewCertificates0227.C7269, NewCertificates0227.C7270, NewCertificates0227.C7271, NewCertificates0227.C7272, NewCertificates0227.C7273, NewCertificates0227.C7274, NewCertificates0227.C7275} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0227.C7276, NewCertificates0227.C7277, NewCertificates0227.C7278, NewCertificates0227.C7279, NewCertificates0227.C7280, NewCertificates0227.C7281, NewCertificates0227.C7282, NewCertificates0227.C7283} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0227.C7284, NewCertificates0227.C7285, NewCertificates0227.C7286, NewCertificates0227.C7287, NewCertificates0227.C7288, NewCertificates0227.C7289, NewCertificates0227.C7290, NewCertificates0227.C7291} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0226.obstruction7260
  · exact NewCertificates0226.obstruction7261
  · exact NewCertificates0226.obstruction7262
  · exact NewCertificates0226.obstruction7263
  · exact NewCertificates0227.obstruction7264
  · exact NewCertificates0227.obstruction7265
  · exact NewCertificates0227.obstruction7266
  · exact NewCertificates0227.obstruction7267
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0227.obstruction7268
  · exact NewCertificates0227.obstruction7269
  · exact NewCertificates0227.obstruction7270
  · exact NewCertificates0227.obstruction7271
  · exact NewCertificates0227.obstruction7272
  · exact NewCertificates0227.obstruction7273
  · exact NewCertificates0227.obstruction7274
  · exact NewCertificates0227.obstruction7275
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0227.obstruction7276
  · exact NewCertificates0227.obstruction7277
  · exact NewCertificates0227.obstruction7278
  · exact NewCertificates0227.obstruction7279
  · exact NewCertificates0227.obstruction7280
  · exact NewCertificates0227.obstruction7281
  · exact NewCertificates0227.obstruction7282
  · exact NewCertificates0227.obstruction7283
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0227.obstruction7284
  · exact NewCertificates0227.obstruction7285
  · exact NewCertificates0227.obstruction7286
  · exact NewCertificates0227.obstruction7287
  · exact NewCertificates0227.obstruction7288
  · exact NewCertificates0227.obstruction7289
  · exact NewCertificates0227.obstruction7290
  · exact NewCertificates0227.obstruction7291
end Nut8.FiniteSupport154
