import SupportData111
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport111
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0168.C5392, NewCertificates0168.C5393, NewCertificates0168.C5394, NewCertificates0168.C5395} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0168.C5396, NewCertificates0168.C5397, NewCertificates0168.C5398, NewCertificates0168.C5399} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0168.C5400, NewCertificates0168.C5401, NewCertificates0168.C5402, NewCertificates0168.C5403} := by
  decide +kernel
theorem signed_enumeration15 : signedPatterns (U15.submatrix e e) p = {NewCertificates0168.C5404, NewCertificates0168.C5405, NewCertificates0168.C5406, NewCertificates0168.C5407} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5392
  · exact NewCertificates0168.obstruction5393
  · exact NewCertificates0168.obstruction5394
  · exact NewCertificates0168.obstruction5395
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5396
  · exact NewCertificates0168.obstruction5397
  · exact NewCertificates0168.obstruction5398
  · exact NewCertificates0168.obstruction5399
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5400
  · exact NewCertificates0168.obstruction5401
  · exact NewCertificates0168.obstruction5402
  · exact NewCertificates0168.obstruction5403
theorem checked15 : ∀ A ∈ signedPatterns (U15.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration15]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5404
  · exact NewCertificates0168.obstruction5405
  · exact NewCertificates0168.obstruction5406
  · exact NewCertificates0168.obstruction5407
end Nut8.FiniteSupport111
