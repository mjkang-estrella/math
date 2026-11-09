import SupportData068
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport068
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0100.C3222, NewCertificates0100.C3223, NewCertificates0100.C3224, NewCertificates0100.C3225, NewCertificates0100.C3226, NewCertificates0100.C3227, NewCertificates0100.C3228, NewCertificates0100.C3229, NewCertificates0100.C3230, NewCertificates0100.C3231, NewCertificates0101.C3232, NewCertificates0101.C3233, NewCertificates0101.C3234, NewCertificates0101.C3235, NewCertificates0101.C3236, NewCertificates0101.C3237} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0101.C3238, NewCertificates0101.C3239, NewCertificates0101.C3240, NewCertificates0101.C3241, NewCertificates0101.C3242, NewCertificates0101.C3243, NewCertificates0101.C3244, NewCertificates0101.C3245} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0100.obstruction3222
  · exact NewCertificates0100.obstruction3223
  · exact NewCertificates0100.obstruction3224
  · exact NewCertificates0100.obstruction3225
  · exact NewCertificates0100.obstruction3226
  · exact NewCertificates0100.obstruction3227
  · exact NewCertificates0100.obstruction3228
  · exact NewCertificates0100.obstruction3229
  · exact NewCertificates0100.obstruction3230
  · exact NewCertificates0100.obstruction3231
  · exact NewCertificates0101.obstruction3232
  · exact NewCertificates0101.obstruction3233
  · exact NewCertificates0101.obstruction3234
  · exact NewCertificates0101.obstruction3235
  · exact NewCertificates0101.obstruction3236
  · exact NewCertificates0101.obstruction3237
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0101.obstruction3238
  · exact NewCertificates0101.obstruction3239
  · exact NewCertificates0101.obstruction3240
  · exact NewCertificates0101.obstruction3241
  · exact NewCertificates0101.obstruction3242
  · exact NewCertificates0101.obstruction3243
  · exact NewCertificates0101.obstruction3244
  · exact NewCertificates0101.obstruction3245
end Nut8.FiniteSupport068
