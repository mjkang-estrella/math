import SupportData154
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport154
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0227.C7292, NewCertificates0227.C7293, NewCertificates0227.C7294, NewCertificates0227.C7295, NewCertificates0228.C7296, NewCertificates0228.C7297, NewCertificates0228.C7298, NewCertificates0228.C7299} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0228.C7300, NewCertificates0228.C7301, NewCertificates0228.C7302, NewCertificates0228.C7303, NewCertificates0228.C7304, NewCertificates0228.C7305, NewCertificates0228.C7306, NewCertificates0228.C7307} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0228.C7308, NewCertificates0228.C7309, NewCertificates0228.C7310, NewCertificates0228.C7311, NewCertificates0228.C7312, NewCertificates0228.C7313, NewCertificates0228.C7314, NewCertificates0228.C7315} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0228.C7316, NewCertificates0228.C7317, NewCertificates0228.C7318, NewCertificates0228.C7319, NewCertificates0228.C7320, NewCertificates0228.C7321, NewCertificates0228.C7322, NewCertificates0228.C7323} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0227.obstruction7292
  · exact NewCertificates0227.obstruction7293
  · exact NewCertificates0227.obstruction7294
  · exact NewCertificates0227.obstruction7295
  · exact NewCertificates0228.obstruction7296
  · exact NewCertificates0228.obstruction7297
  · exact NewCertificates0228.obstruction7298
  · exact NewCertificates0228.obstruction7299
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0228.obstruction7300
  · exact NewCertificates0228.obstruction7301
  · exact NewCertificates0228.obstruction7302
  · exact NewCertificates0228.obstruction7303
  · exact NewCertificates0228.obstruction7304
  · exact NewCertificates0228.obstruction7305
  · exact NewCertificates0228.obstruction7306
  · exact NewCertificates0228.obstruction7307
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0228.obstruction7308
  · exact NewCertificates0228.obstruction7309
  · exact NewCertificates0228.obstruction7310
  · exact NewCertificates0228.obstruction7311
  · exact NewCertificates0228.obstruction7312
  · exact NewCertificates0228.obstruction7313
  · exact NewCertificates0228.obstruction7314
  · exact NewCertificates0228.obstruction7315
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0228.obstruction7316
  · exact NewCertificates0228.obstruction7317
  · exact NewCertificates0228.obstruction7318
  · exact NewCertificates0228.obstruction7319
  · exact NewCertificates0228.obstruction7320
  · exact NewCertificates0228.obstruction7321
  · exact NewCertificates0228.obstruction7322
  · exact NewCertificates0228.obstruction7323
end Nut8.FiniteSupport154
