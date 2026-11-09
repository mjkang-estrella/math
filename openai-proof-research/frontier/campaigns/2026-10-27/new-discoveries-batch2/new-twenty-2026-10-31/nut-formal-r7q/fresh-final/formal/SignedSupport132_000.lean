import SupportData132
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport132
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0195.C6260, NewCertificates0195.C6261, NewCertificates0195.C6262, NewCertificates0195.C6263, NewCertificates0195.C6264, NewCertificates0195.C6265, NewCertificates0195.C6266, NewCertificates0195.C6267, NewCertificates0195.C6268, NewCertificates0195.C6269, NewCertificates0195.C6270, NewCertificates0195.C6271, NewCertificates0196.C6272, NewCertificates0196.C6273, NewCertificates0196.C6274, NewCertificates0196.C6275, NewCertificates0196.C6276, NewCertificates0196.C6277, NewCertificates0196.C6278, NewCertificates0196.C6279, NewCertificates0196.C6280, NewCertificates0196.C6281, NewCertificates0196.C6282, NewCertificates0196.C6283, NewCertificates0196.C6284, NewCertificates0196.C6285, NewCertificates0196.C6286, NewCertificates0196.C6287, NewCertificates0196.C6288, NewCertificates0196.C6289, NewCertificates0196.C6290, NewCertificates0196.C6291} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0195.obstruction6260
  · exact NewCertificates0195.obstruction6261
  · exact NewCertificates0195.obstruction6262
  · exact NewCertificates0195.obstruction6263
  · exact NewCertificates0195.obstruction6264
  · exact NewCertificates0195.obstruction6265
  · exact NewCertificates0195.obstruction6266
  · exact NewCertificates0195.obstruction6267
  · exact NewCertificates0195.obstruction6268
  · exact NewCertificates0195.obstruction6269
  · exact NewCertificates0195.obstruction6270
  · exact NewCertificates0195.obstruction6271
  · exact NewCertificates0196.obstruction6272
  · exact NewCertificates0196.obstruction6273
  · exact NewCertificates0196.obstruction6274
  · exact NewCertificates0196.obstruction6275
  · exact NewCertificates0196.obstruction6276
  · exact NewCertificates0196.obstruction6277
  · exact NewCertificates0196.obstruction6278
  · exact NewCertificates0196.obstruction6279
  · exact NewCertificates0196.obstruction6280
  · exact NewCertificates0196.obstruction6281
  · exact NewCertificates0196.obstruction6282
  · exact NewCertificates0196.obstruction6283
  · exact NewCertificates0196.obstruction6284
  · exact NewCertificates0196.obstruction6285
  · exact NewCertificates0196.obstruction6286
  · exact NewCertificates0196.obstruction6287
  · exact NewCertificates0196.obstruction6288
  · exact NewCertificates0196.obstruction6289
  · exact NewCertificates0196.obstruction6290
  · exact NewCertificates0196.obstruction6291
end Nut8.FiniteSupport132
