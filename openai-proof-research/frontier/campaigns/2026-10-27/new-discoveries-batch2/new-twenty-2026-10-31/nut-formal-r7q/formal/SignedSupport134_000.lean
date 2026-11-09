import SupportData134
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport134
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0197.C6324, NewCertificates0197.C6325, NewCertificates0197.C6326, NewCertificates0197.C6327, NewCertificates0197.C6328, NewCertificates0197.C6329, NewCertificates0197.C6330, NewCertificates0197.C6331, NewCertificates0197.C6332, NewCertificates0197.C6333, NewCertificates0197.C6334, NewCertificates0197.C6335, NewCertificates0198.C6336, NewCertificates0198.C6337, NewCertificates0198.C6338, NewCertificates0198.C6339, NewCertificates0198.C6340, NewCertificates0198.C6341, NewCertificates0198.C6342, NewCertificates0198.C6343, NewCertificates0198.C6344, NewCertificates0198.C6345, NewCertificates0198.C6346, NewCertificates0198.C6347, NewCertificates0198.C6348, NewCertificates0198.C6349, NewCertificates0198.C6350, NewCertificates0198.C6351, NewCertificates0198.C6352, NewCertificates0198.C6353, NewCertificates0198.C6354, NewCertificates0198.C6355} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0197.obstruction6324
  · exact NewCertificates0197.obstruction6325
  · exact NewCertificates0197.obstruction6326
  · exact NewCertificates0197.obstruction6327
  · exact NewCertificates0197.obstruction6328
  · exact NewCertificates0197.obstruction6329
  · exact NewCertificates0197.obstruction6330
  · exact NewCertificates0197.obstruction6331
  · exact NewCertificates0197.obstruction6332
  · exact NewCertificates0197.obstruction6333
  · exact NewCertificates0197.obstruction6334
  · exact NewCertificates0197.obstruction6335
  · exact NewCertificates0198.obstruction6336
  · exact NewCertificates0198.obstruction6337
  · exact NewCertificates0198.obstruction6338
  · exact NewCertificates0198.obstruction6339
  · exact NewCertificates0198.obstruction6340
  · exact NewCertificates0198.obstruction6341
  · exact NewCertificates0198.obstruction6342
  · exact NewCertificates0198.obstruction6343
  · exact NewCertificates0198.obstruction6344
  · exact NewCertificates0198.obstruction6345
  · exact NewCertificates0198.obstruction6346
  · exact NewCertificates0198.obstruction6347
  · exact NewCertificates0198.obstruction6348
  · exact NewCertificates0198.obstruction6349
  · exact NewCertificates0198.obstruction6350
  · exact NewCertificates0198.obstruction6351
  · exact NewCertificates0198.obstruction6352
  · exact NewCertificates0198.obstruction6353
  · exact NewCertificates0198.obstruction6354
  · exact NewCertificates0198.obstruction6355
end Nut8.FiniteSupport134
