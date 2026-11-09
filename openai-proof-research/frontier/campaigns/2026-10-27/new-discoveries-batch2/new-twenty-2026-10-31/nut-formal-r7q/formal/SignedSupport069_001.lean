import SupportData069
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport069
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0103.C3302, NewCertificates0103.C3303, NewCertificates0103.C3304, NewCertificates0103.C3305, NewCertificates0103.C3306, NewCertificates0103.C3307, NewCertificates0103.C3308, NewCertificates0103.C3309} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0103.C3310, NewCertificates0103.C3311, NewCertificates0103.C3312, NewCertificates0103.C3313, NewCertificates0103.C3314, NewCertificates0103.C3315, NewCertificates0103.C3316, NewCertificates0103.C3317} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0103.obstruction3302
  · exact NewCertificates0103.obstruction3303
  · exact NewCertificates0103.obstruction3304
  · exact NewCertificates0103.obstruction3305
  · exact NewCertificates0103.obstruction3306
  · exact NewCertificates0103.obstruction3307
  · exact NewCertificates0103.obstruction3308
  · exact NewCertificates0103.obstruction3309
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0103.obstruction3310
  · exact NewCertificates0103.obstruction3311
  · exact NewCertificates0103.obstruction3312
  · exact NewCertificates0103.obstruction3313
  · exact NewCertificates0103.obstruction3314
  · exact NewCertificates0103.obstruction3315
  · exact NewCertificates0103.obstruction3316
  · exact NewCertificates0103.obstruction3317
end Nut8.FiniteSupport069
