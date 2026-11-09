import SupportData110
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport110
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0165.C5280, NewCertificates0165.C5281, NewCertificates0165.C5282, NewCertificates0165.C5283, NewCertificates0165.C5284, NewCertificates0165.C5285, NewCertificates0165.C5286, NewCertificates0165.C5287} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0165.C5288, NewCertificates0165.C5289, NewCertificates0165.C5290, NewCertificates0165.C5291} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0165.C5292, NewCertificates0165.C5293, NewCertificates0165.C5294, NewCertificates0165.C5295} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0165.C5296, NewCertificates0165.C5297, NewCertificates0165.C5298, NewCertificates0165.C5299} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5280
  · exact NewCertificates0165.obstruction5281
  · exact NewCertificates0165.obstruction5282
  · exact NewCertificates0165.obstruction5283
  · exact NewCertificates0165.obstruction5284
  · exact NewCertificates0165.obstruction5285
  · exact NewCertificates0165.obstruction5286
  · exact NewCertificates0165.obstruction5287
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5288
  · exact NewCertificates0165.obstruction5289
  · exact NewCertificates0165.obstruction5290
  · exact NewCertificates0165.obstruction5291
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5292
  · exact NewCertificates0165.obstruction5293
  · exact NewCertificates0165.obstruction5294
  · exact NewCertificates0165.obstruction5295
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5296
  · exact NewCertificates0165.obstruction5297
  · exact NewCertificates0165.obstruction5298
  · exact NewCertificates0165.obstruction5299
end Nut8.FiniteSupport110
