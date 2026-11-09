import SupportData157
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport157
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0232.C7432, NewCertificates0232.C7433, NewCertificates0232.C7434, NewCertificates0232.C7435, NewCertificates0232.C7436, NewCertificates0232.C7437, NewCertificates0232.C7438, NewCertificates0232.C7439} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0232.C7440, NewCertificates0232.C7441, NewCertificates0232.C7442, NewCertificates0232.C7443, NewCertificates0232.C7444, NewCertificates0232.C7445, NewCertificates0232.C7446, NewCertificates0232.C7447} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0232.C7448, NewCertificates0232.C7449, NewCertificates0232.C7450, NewCertificates0232.C7451, NewCertificates0232.C7452, NewCertificates0232.C7453, NewCertificates0232.C7454, NewCertificates0232.C7455} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0233.C7456, NewCertificates0233.C7457, NewCertificates0233.C7458, NewCertificates0233.C7459, NewCertificates0233.C7460, NewCertificates0233.C7461, NewCertificates0233.C7462, NewCertificates0233.C7463} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0232.obstruction7432
  · exact NewCertificates0232.obstruction7433
  · exact NewCertificates0232.obstruction7434
  · exact NewCertificates0232.obstruction7435
  · exact NewCertificates0232.obstruction7436
  · exact NewCertificates0232.obstruction7437
  · exact NewCertificates0232.obstruction7438
  · exact NewCertificates0232.obstruction7439
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0232.obstruction7440
  · exact NewCertificates0232.obstruction7441
  · exact NewCertificates0232.obstruction7442
  · exact NewCertificates0232.obstruction7443
  · exact NewCertificates0232.obstruction7444
  · exact NewCertificates0232.obstruction7445
  · exact NewCertificates0232.obstruction7446
  · exact NewCertificates0232.obstruction7447
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0232.obstruction7448
  · exact NewCertificates0232.obstruction7449
  · exact NewCertificates0232.obstruction7450
  · exact NewCertificates0232.obstruction7451
  · exact NewCertificates0232.obstruction7452
  · exact NewCertificates0232.obstruction7453
  · exact NewCertificates0232.obstruction7454
  · exact NewCertificates0232.obstruction7455
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0233.obstruction7456
  · exact NewCertificates0233.obstruction7457
  · exact NewCertificates0233.obstruction7458
  · exact NewCertificates0233.obstruction7459
  · exact NewCertificates0233.obstruction7460
  · exact NewCertificates0233.obstruction7461
  · exact NewCertificates0233.obstruction7462
  · exact NewCertificates0233.obstruction7463
end Nut8.FiniteSupport157
