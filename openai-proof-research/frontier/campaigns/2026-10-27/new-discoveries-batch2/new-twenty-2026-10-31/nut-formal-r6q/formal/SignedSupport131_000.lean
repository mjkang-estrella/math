import SupportData131
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport131
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0194.C6228, NewCertificates0194.C6229, NewCertificates0194.C6230, NewCertificates0194.C6231, NewCertificates0194.C6232, NewCertificates0194.C6233, NewCertificates0194.C6234, NewCertificates0194.C6235, NewCertificates0194.C6236, NewCertificates0194.C6237, NewCertificates0194.C6238, NewCertificates0194.C6239, NewCertificates0195.C6240, NewCertificates0195.C6241, NewCertificates0195.C6242, NewCertificates0195.C6243} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0195.C6244, NewCertificates0195.C6245, NewCertificates0195.C6246, NewCertificates0195.C6247, NewCertificates0195.C6248, NewCertificates0195.C6249, NewCertificates0195.C6250, NewCertificates0195.C6251, NewCertificates0195.C6252, NewCertificates0195.C6253, NewCertificates0195.C6254, NewCertificates0195.C6255, NewCertificates0195.C6256, NewCertificates0195.C6257, NewCertificates0195.C6258, NewCertificates0195.C6259} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0194.obstruction6228
  · exact NewCertificates0194.obstruction6229
  · exact NewCertificates0194.obstruction6230
  · exact NewCertificates0194.obstruction6231
  · exact NewCertificates0194.obstruction6232
  · exact NewCertificates0194.obstruction6233
  · exact NewCertificates0194.obstruction6234
  · exact NewCertificates0194.obstruction6235
  · exact NewCertificates0194.obstruction6236
  · exact NewCertificates0194.obstruction6237
  · exact NewCertificates0194.obstruction6238
  · exact NewCertificates0194.obstruction6239
  · exact NewCertificates0195.obstruction6240
  · exact NewCertificates0195.obstruction6241
  · exact NewCertificates0195.obstruction6242
  · exact NewCertificates0195.obstruction6243
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0195.obstruction6244
  · exact NewCertificates0195.obstruction6245
  · exact NewCertificates0195.obstruction6246
  · exact NewCertificates0195.obstruction6247
  · exact NewCertificates0195.obstruction6248
  · exact NewCertificates0195.obstruction6249
  · exact NewCertificates0195.obstruction6250
  · exact NewCertificates0195.obstruction6251
  · exact NewCertificates0195.obstruction6252
  · exact NewCertificates0195.obstruction6253
  · exact NewCertificates0195.obstruction6254
  · exact NewCertificates0195.obstruction6255
  · exact NewCertificates0195.obstruction6256
  · exact NewCertificates0195.obstruction6257
  · exact NewCertificates0195.obstruction6258
  · exact NewCertificates0195.obstruction6259
end Nut8.FiniteSupport131
