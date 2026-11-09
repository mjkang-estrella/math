import SupportData112
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport112
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0171.C5492, NewCertificates0171.C5493, NewCertificates0171.C5494, NewCertificates0171.C5495} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0171.C5496, NewCertificates0171.C5497, NewCertificates0171.C5498, NewCertificates0171.C5499} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0171.C5500, NewCertificates0171.C5501, NewCertificates0171.C5502, NewCertificates0171.C5503} := by
  decide +kernel
theorem signed_enumeration15 : signedPatterns (U15.submatrix e e) p = {NewCertificates0172.C5504, NewCertificates0172.C5505, NewCertificates0172.C5506, NewCertificates0172.C5507} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5492
  · exact NewCertificates0171.obstruction5493
  · exact NewCertificates0171.obstruction5494
  · exact NewCertificates0171.obstruction5495
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5496
  · exact NewCertificates0171.obstruction5497
  · exact NewCertificates0171.obstruction5498
  · exact NewCertificates0171.obstruction5499
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5500
  · exact NewCertificates0171.obstruction5501
  · exact NewCertificates0171.obstruction5502
  · exact NewCertificates0171.obstruction5503
theorem checked15 : ∀ A ∈ signedPatterns (U15.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration15]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0172.obstruction5504
  · exact NewCertificates0172.obstruction5505
  · exact NewCertificates0172.obstruction5506
  · exact NewCertificates0172.obstruction5507
end Nut8.FiniteSupport112
