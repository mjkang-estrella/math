import SupportData112
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport112
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0170.C5440, NewCertificates0170.C5441, NewCertificates0170.C5442, NewCertificates0170.C5443, NewCertificates0170.C5444, NewCertificates0170.C5445, NewCertificates0170.C5446, NewCertificates0170.C5447} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0170.C5448, NewCertificates0170.C5449, NewCertificates0170.C5450, NewCertificates0170.C5451, NewCertificates0170.C5452, NewCertificates0170.C5453, NewCertificates0170.C5454, NewCertificates0170.C5455} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0170.C5456, NewCertificates0170.C5457, NewCertificates0170.C5458, NewCertificates0170.C5459, NewCertificates0170.C5460, NewCertificates0170.C5461, NewCertificates0170.C5462, NewCertificates0170.C5463} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0170.C5464, NewCertificates0170.C5465, NewCertificates0170.C5466, NewCertificates0170.C5467, NewCertificates0170.C5468, NewCertificates0170.C5469, NewCertificates0170.C5470, NewCertificates0170.C5471} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0170.obstruction5440
  · exact NewCertificates0170.obstruction5441
  · exact NewCertificates0170.obstruction5442
  · exact NewCertificates0170.obstruction5443
  · exact NewCertificates0170.obstruction5444
  · exact NewCertificates0170.obstruction5445
  · exact NewCertificates0170.obstruction5446
  · exact NewCertificates0170.obstruction5447
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0170.obstruction5448
  · exact NewCertificates0170.obstruction5449
  · exact NewCertificates0170.obstruction5450
  · exact NewCertificates0170.obstruction5451
  · exact NewCertificates0170.obstruction5452
  · exact NewCertificates0170.obstruction5453
  · exact NewCertificates0170.obstruction5454
  · exact NewCertificates0170.obstruction5455
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0170.obstruction5456
  · exact NewCertificates0170.obstruction5457
  · exact NewCertificates0170.obstruction5458
  · exact NewCertificates0170.obstruction5459
  · exact NewCertificates0170.obstruction5460
  · exact NewCertificates0170.obstruction5461
  · exact NewCertificates0170.obstruction5462
  · exact NewCertificates0170.obstruction5463
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0170.obstruction5464
  · exact NewCertificates0170.obstruction5465
  · exact NewCertificates0170.obstruction5466
  · exact NewCertificates0170.obstruction5467
  · exact NewCertificates0170.obstruction5468
  · exact NewCertificates0170.obstruction5469
  · exact NewCertificates0170.obstruction5470
  · exact NewCertificates0170.obstruction5471
end Nut8.FiniteSupport112
