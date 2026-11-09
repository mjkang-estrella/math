import SupportData070
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport070
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0105.C3366, NewCertificates0105.C3367, NewCertificates0105.C3368, NewCertificates0105.C3369, NewCertificates0105.C3370, NewCertificates0105.C3371, NewCertificates0105.C3372, NewCertificates0105.C3373, NewCertificates0105.C3374, NewCertificates0105.C3375, NewCertificates0105.C3376, NewCertificates0105.C3377, NewCertificates0105.C3378, NewCertificates0105.C3379, NewCertificates0105.C3380, NewCertificates0105.C3381} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0105.C3382, NewCertificates0105.C3383, NewCertificates0105.C3384, NewCertificates0105.C3385, NewCertificates0105.C3386, NewCertificates0105.C3387, NewCertificates0105.C3388, NewCertificates0105.C3389} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0105.obstruction3366
  · exact NewCertificates0105.obstruction3367
  · exact NewCertificates0105.obstruction3368
  · exact NewCertificates0105.obstruction3369
  · exact NewCertificates0105.obstruction3370
  · exact NewCertificates0105.obstruction3371
  · exact NewCertificates0105.obstruction3372
  · exact NewCertificates0105.obstruction3373
  · exact NewCertificates0105.obstruction3374
  · exact NewCertificates0105.obstruction3375
  · exact NewCertificates0105.obstruction3376
  · exact NewCertificates0105.obstruction3377
  · exact NewCertificates0105.obstruction3378
  · exact NewCertificates0105.obstruction3379
  · exact NewCertificates0105.obstruction3380
  · exact NewCertificates0105.obstruction3381
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0105.obstruction3382
  · exact NewCertificates0105.obstruction3383
  · exact NewCertificates0105.obstruction3384
  · exact NewCertificates0105.obstruction3385
  · exact NewCertificates0105.obstruction3386
  · exact NewCertificates0105.obstruction3387
  · exact NewCertificates0105.obstruction3388
  · exact NewCertificates0105.obstruction3389
end Nut8.FiniteSupport070
