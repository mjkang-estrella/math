import SupportData111
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport111
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0168.C5376, NewCertificates0168.C5377, NewCertificates0168.C5378, NewCertificates0168.C5379} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0168.C5380, NewCertificates0168.C5381, NewCertificates0168.C5382, NewCertificates0168.C5383} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0168.C5384, NewCertificates0168.C5385, NewCertificates0168.C5386, NewCertificates0168.C5387} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0168.C5388, NewCertificates0168.C5389, NewCertificates0168.C5390, NewCertificates0168.C5391} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5376
  · exact NewCertificates0168.obstruction5377
  · exact NewCertificates0168.obstruction5378
  · exact NewCertificates0168.obstruction5379
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5380
  · exact NewCertificates0168.obstruction5381
  · exact NewCertificates0168.obstruction5382
  · exact NewCertificates0168.obstruction5383
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5384
  · exact NewCertificates0168.obstruction5385
  · exact NewCertificates0168.obstruction5386
  · exact NewCertificates0168.obstruction5387
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0168.obstruction5388
  · exact NewCertificates0168.obstruction5389
  · exact NewCertificates0168.obstruction5390
  · exact NewCertificates0168.obstruction5391
end Nut8.FiniteSupport111
