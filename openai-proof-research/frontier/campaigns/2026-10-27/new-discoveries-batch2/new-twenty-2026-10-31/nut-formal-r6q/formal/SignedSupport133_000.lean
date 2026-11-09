import SupportData133
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport133
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0196.C6292, NewCertificates0196.C6293, NewCertificates0196.C6294, NewCertificates0196.C6295, NewCertificates0196.C6296, NewCertificates0196.C6297, NewCertificates0196.C6298, NewCertificates0196.C6299, NewCertificates0196.C6300, NewCertificates0196.C6301, NewCertificates0196.C6302, NewCertificates0196.C6303, NewCertificates0197.C6304, NewCertificates0197.C6305, NewCertificates0197.C6306, NewCertificates0197.C6307, NewCertificates0197.C6308, NewCertificates0197.C6309, NewCertificates0197.C6310, NewCertificates0197.C6311, NewCertificates0197.C6312, NewCertificates0197.C6313, NewCertificates0197.C6314, NewCertificates0197.C6315, NewCertificates0197.C6316, NewCertificates0197.C6317, NewCertificates0197.C6318, NewCertificates0197.C6319, NewCertificates0197.C6320, NewCertificates0197.C6321, NewCertificates0197.C6322, NewCertificates0197.C6323} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0196.obstruction6292
  · exact NewCertificates0196.obstruction6293
  · exact NewCertificates0196.obstruction6294
  · exact NewCertificates0196.obstruction6295
  · exact NewCertificates0196.obstruction6296
  · exact NewCertificates0196.obstruction6297
  · exact NewCertificates0196.obstruction6298
  · exact NewCertificates0196.obstruction6299
  · exact NewCertificates0196.obstruction6300
  · exact NewCertificates0196.obstruction6301
  · exact NewCertificates0196.obstruction6302
  · exact NewCertificates0196.obstruction6303
  · exact NewCertificates0197.obstruction6304
  · exact NewCertificates0197.obstruction6305
  · exact NewCertificates0197.obstruction6306
  · exact NewCertificates0197.obstruction6307
  · exact NewCertificates0197.obstruction6308
  · exact NewCertificates0197.obstruction6309
  · exact NewCertificates0197.obstruction6310
  · exact NewCertificates0197.obstruction6311
  · exact NewCertificates0197.obstruction6312
  · exact NewCertificates0197.obstruction6313
  · exact NewCertificates0197.obstruction6314
  · exact NewCertificates0197.obstruction6315
  · exact NewCertificates0197.obstruction6316
  · exact NewCertificates0197.obstruction6317
  · exact NewCertificates0197.obstruction6318
  · exact NewCertificates0197.obstruction6319
  · exact NewCertificates0197.obstruction6320
  · exact NewCertificates0197.obstruction6321
  · exact NewCertificates0197.obstruction6322
  · exact NewCertificates0197.obstruction6323
end Nut8.FiniteSupport133
