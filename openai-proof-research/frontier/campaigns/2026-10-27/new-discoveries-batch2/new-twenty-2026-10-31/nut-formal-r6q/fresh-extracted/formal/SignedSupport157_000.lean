import SupportData157
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport157
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0231.C7400, NewCertificates0231.C7401, NewCertificates0231.C7402, NewCertificates0231.C7403, NewCertificates0231.C7404, NewCertificates0231.C7405, NewCertificates0231.C7406, NewCertificates0231.C7407} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0231.C7408, NewCertificates0231.C7409, NewCertificates0231.C7410, NewCertificates0231.C7411, NewCertificates0231.C7412, NewCertificates0231.C7413, NewCertificates0231.C7414, NewCertificates0231.C7415} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0231.C7416, NewCertificates0231.C7417, NewCertificates0231.C7418, NewCertificates0231.C7419, NewCertificates0231.C7420, NewCertificates0231.C7421, NewCertificates0231.C7422, NewCertificates0231.C7423} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0232.C7424, NewCertificates0232.C7425, NewCertificates0232.C7426, NewCertificates0232.C7427, NewCertificates0232.C7428, NewCertificates0232.C7429, NewCertificates0232.C7430, NewCertificates0232.C7431} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0231.obstruction7400
  · exact NewCertificates0231.obstruction7401
  · exact NewCertificates0231.obstruction7402
  · exact NewCertificates0231.obstruction7403
  · exact NewCertificates0231.obstruction7404
  · exact NewCertificates0231.obstruction7405
  · exact NewCertificates0231.obstruction7406
  · exact NewCertificates0231.obstruction7407
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0231.obstruction7408
  · exact NewCertificates0231.obstruction7409
  · exact NewCertificates0231.obstruction7410
  · exact NewCertificates0231.obstruction7411
  · exact NewCertificates0231.obstruction7412
  · exact NewCertificates0231.obstruction7413
  · exact NewCertificates0231.obstruction7414
  · exact NewCertificates0231.obstruction7415
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0231.obstruction7416
  · exact NewCertificates0231.obstruction7417
  · exact NewCertificates0231.obstruction7418
  · exact NewCertificates0231.obstruction7419
  · exact NewCertificates0231.obstruction7420
  · exact NewCertificates0231.obstruction7421
  · exact NewCertificates0231.obstruction7422
  · exact NewCertificates0231.obstruction7423
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0232.obstruction7424
  · exact NewCertificates0232.obstruction7425
  · exact NewCertificates0232.obstruction7426
  · exact NewCertificates0232.obstruction7427
  · exact NewCertificates0232.obstruction7428
  · exact NewCertificates0232.obstruction7429
  · exact NewCertificates0232.obstruction7430
  · exact NewCertificates0232.obstruction7431
end Nut8.FiniteSupport157
