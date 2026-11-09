import SupportData111
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport111
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0167.C5344, NewCertificates0167.C5345, NewCertificates0167.C5346, NewCertificates0167.C5347, NewCertificates0167.C5348, NewCertificates0167.C5349, NewCertificates0167.C5350, NewCertificates0167.C5351} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0167.C5352, NewCertificates0167.C5353, NewCertificates0167.C5354, NewCertificates0167.C5355, NewCertificates0167.C5356, NewCertificates0167.C5357, NewCertificates0167.C5358, NewCertificates0167.C5359} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0167.C5360, NewCertificates0167.C5361, NewCertificates0167.C5362, NewCertificates0167.C5363, NewCertificates0167.C5364, NewCertificates0167.C5365, NewCertificates0167.C5366, NewCertificates0167.C5367} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0167.C5368, NewCertificates0167.C5369, NewCertificates0167.C5370, NewCertificates0167.C5371, NewCertificates0167.C5372, NewCertificates0167.C5373, NewCertificates0167.C5374, NewCertificates0167.C5375} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0167.obstruction5344
  · exact NewCertificates0167.obstruction5345
  · exact NewCertificates0167.obstruction5346
  · exact NewCertificates0167.obstruction5347
  · exact NewCertificates0167.obstruction5348
  · exact NewCertificates0167.obstruction5349
  · exact NewCertificates0167.obstruction5350
  · exact NewCertificates0167.obstruction5351
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0167.obstruction5352
  · exact NewCertificates0167.obstruction5353
  · exact NewCertificates0167.obstruction5354
  · exact NewCertificates0167.obstruction5355
  · exact NewCertificates0167.obstruction5356
  · exact NewCertificates0167.obstruction5357
  · exact NewCertificates0167.obstruction5358
  · exact NewCertificates0167.obstruction5359
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0167.obstruction5360
  · exact NewCertificates0167.obstruction5361
  · exact NewCertificates0167.obstruction5362
  · exact NewCertificates0167.obstruction5363
  · exact NewCertificates0167.obstruction5364
  · exact NewCertificates0167.obstruction5365
  · exact NewCertificates0167.obstruction5366
  · exact NewCertificates0167.obstruction5367
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0167.obstruction5368
  · exact NewCertificates0167.obstruction5369
  · exact NewCertificates0167.obstruction5370
  · exact NewCertificates0167.obstruction5371
  · exact NewCertificates0167.obstruction5372
  · exact NewCertificates0167.obstruction5373
  · exact NewCertificates0167.obstruction5374
  · exact NewCertificates0167.obstruction5375
end Nut8.FiniteSupport111
