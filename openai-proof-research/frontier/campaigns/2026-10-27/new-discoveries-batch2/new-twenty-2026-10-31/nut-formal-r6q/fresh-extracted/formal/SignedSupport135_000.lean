import SupportData135
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport135
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0198.C6356, NewCertificates0198.C6357, NewCertificates0198.C6358, NewCertificates0198.C6359, NewCertificates0198.C6360, NewCertificates0198.C6361, NewCertificates0198.C6362, NewCertificates0198.C6363, NewCertificates0198.C6364, NewCertificates0198.C6365, NewCertificates0198.C6366, NewCertificates0198.C6367, NewCertificates0199.C6368, NewCertificates0199.C6369, NewCertificates0199.C6370, NewCertificates0199.C6371} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0199.C6372, NewCertificates0199.C6373, NewCertificates0199.C6374, NewCertificates0199.C6375, NewCertificates0199.C6376, NewCertificates0199.C6377, NewCertificates0199.C6378, NewCertificates0199.C6379, NewCertificates0199.C6380, NewCertificates0199.C6381, NewCertificates0199.C6382, NewCertificates0199.C6383, NewCertificates0199.C6384, NewCertificates0199.C6385, NewCertificates0199.C6386, NewCertificates0199.C6387} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0198.obstruction6356
  · exact NewCertificates0198.obstruction6357
  · exact NewCertificates0198.obstruction6358
  · exact NewCertificates0198.obstruction6359
  · exact NewCertificates0198.obstruction6360
  · exact NewCertificates0198.obstruction6361
  · exact NewCertificates0198.obstruction6362
  · exact NewCertificates0198.obstruction6363
  · exact NewCertificates0198.obstruction6364
  · exact NewCertificates0198.obstruction6365
  · exact NewCertificates0198.obstruction6366
  · exact NewCertificates0198.obstruction6367
  · exact NewCertificates0199.obstruction6368
  · exact NewCertificates0199.obstruction6369
  · exact NewCertificates0199.obstruction6370
  · exact NewCertificates0199.obstruction6371
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0199.obstruction6372
  · exact NewCertificates0199.obstruction6373
  · exact NewCertificates0199.obstruction6374
  · exact NewCertificates0199.obstruction6375
  · exact NewCertificates0199.obstruction6376
  · exact NewCertificates0199.obstruction6377
  · exact NewCertificates0199.obstruction6378
  · exact NewCertificates0199.obstruction6379
  · exact NewCertificates0199.obstruction6380
  · exact NewCertificates0199.obstruction6381
  · exact NewCertificates0199.obstruction6382
  · exact NewCertificates0199.obstruction6383
  · exact NewCertificates0199.obstruction6384
  · exact NewCertificates0199.obstruction6385
  · exact NewCertificates0199.obstruction6386
  · exact NewCertificates0199.obstruction6387
end Nut8.FiniteSupport135
