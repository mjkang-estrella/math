import SupportData112
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport112
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0169.C5408, NewCertificates0169.C5409, NewCertificates0169.C5410, NewCertificates0169.C5411, NewCertificates0169.C5412, NewCertificates0169.C5413, NewCertificates0169.C5414, NewCertificates0169.C5415} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0169.C5416, NewCertificates0169.C5417, NewCertificates0169.C5418, NewCertificates0169.C5419, NewCertificates0169.C5420, NewCertificates0169.C5421, NewCertificates0169.C5422, NewCertificates0169.C5423} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0169.C5424, NewCertificates0169.C5425, NewCertificates0169.C5426, NewCertificates0169.C5427, NewCertificates0169.C5428, NewCertificates0169.C5429, NewCertificates0169.C5430, NewCertificates0169.C5431} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0169.C5432, NewCertificates0169.C5433, NewCertificates0169.C5434, NewCertificates0169.C5435, NewCertificates0169.C5436, NewCertificates0169.C5437, NewCertificates0169.C5438, NewCertificates0169.C5439} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0169.obstruction5408
  · exact NewCertificates0169.obstruction5409
  · exact NewCertificates0169.obstruction5410
  · exact NewCertificates0169.obstruction5411
  · exact NewCertificates0169.obstruction5412
  · exact NewCertificates0169.obstruction5413
  · exact NewCertificates0169.obstruction5414
  · exact NewCertificates0169.obstruction5415
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0169.obstruction5416
  · exact NewCertificates0169.obstruction5417
  · exact NewCertificates0169.obstruction5418
  · exact NewCertificates0169.obstruction5419
  · exact NewCertificates0169.obstruction5420
  · exact NewCertificates0169.obstruction5421
  · exact NewCertificates0169.obstruction5422
  · exact NewCertificates0169.obstruction5423
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0169.obstruction5424
  · exact NewCertificates0169.obstruction5425
  · exact NewCertificates0169.obstruction5426
  · exact NewCertificates0169.obstruction5427
  · exact NewCertificates0169.obstruction5428
  · exact NewCertificates0169.obstruction5429
  · exact NewCertificates0169.obstruction5430
  · exact NewCertificates0169.obstruction5431
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0169.obstruction5432
  · exact NewCertificates0169.obstruction5433
  · exact NewCertificates0169.obstruction5434
  · exact NewCertificates0169.obstruction5435
  · exact NewCertificates0169.obstruction5436
  · exact NewCertificates0169.obstruction5437
  · exact NewCertificates0169.obstruction5438
  · exact NewCertificates0169.obstruction5439
end Nut8.FiniteSupport112
