import SupportData155
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport155
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0229.C7336, NewCertificates0229.C7337, NewCertificates0229.C7338, NewCertificates0229.C7339, NewCertificates0229.C7340, NewCertificates0229.C7341, NewCertificates0229.C7342, NewCertificates0229.C7343, NewCertificates0229.C7344, NewCertificates0229.C7345, NewCertificates0229.C7346, NewCertificates0229.C7347, NewCertificates0229.C7348, NewCertificates0229.C7349, NewCertificates0229.C7350, NewCertificates0229.C7351} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0229.C7352, NewCertificates0229.C7353, NewCertificates0229.C7354, NewCertificates0229.C7355, NewCertificates0229.C7356, NewCertificates0229.C7357, NewCertificates0229.C7358, NewCertificates0229.C7359, NewCertificates0230.C7360, NewCertificates0230.C7361, NewCertificates0230.C7362, NewCertificates0230.C7363, NewCertificates0230.C7364, NewCertificates0230.C7365, NewCertificates0230.C7366, NewCertificates0230.C7367} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0229.obstruction7336
  · exact NewCertificates0229.obstruction7337
  · exact NewCertificates0229.obstruction7338
  · exact NewCertificates0229.obstruction7339
  · exact NewCertificates0229.obstruction7340
  · exact NewCertificates0229.obstruction7341
  · exact NewCertificates0229.obstruction7342
  · exact NewCertificates0229.obstruction7343
  · exact NewCertificates0229.obstruction7344
  · exact NewCertificates0229.obstruction7345
  · exact NewCertificates0229.obstruction7346
  · exact NewCertificates0229.obstruction7347
  · exact NewCertificates0229.obstruction7348
  · exact NewCertificates0229.obstruction7349
  · exact NewCertificates0229.obstruction7350
  · exact NewCertificates0229.obstruction7351
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0229.obstruction7352
  · exact NewCertificates0229.obstruction7353
  · exact NewCertificates0229.obstruction7354
  · exact NewCertificates0229.obstruction7355
  · exact NewCertificates0229.obstruction7356
  · exact NewCertificates0229.obstruction7357
  · exact NewCertificates0229.obstruction7358
  · exact NewCertificates0229.obstruction7359
  · exact NewCertificates0230.obstruction7360
  · exact NewCertificates0230.obstruction7361
  · exact NewCertificates0230.obstruction7362
  · exact NewCertificates0230.obstruction7363
  · exact NewCertificates0230.obstruction7364
  · exact NewCertificates0230.obstruction7365
  · exact NewCertificates0230.obstruction7366
  · exact NewCertificates0230.obstruction7367
end Nut8.FiniteSupport155
