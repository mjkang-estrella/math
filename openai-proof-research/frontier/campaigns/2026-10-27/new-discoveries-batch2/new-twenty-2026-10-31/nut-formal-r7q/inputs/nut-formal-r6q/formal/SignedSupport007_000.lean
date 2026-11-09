import SupportData007
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport007
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0011.C352, NewCertificates0011.C353, NewCertificates0011.C354, NewCertificates0011.C355, NewCertificates0011.C356, NewCertificates0011.C357, NewCertificates0011.C358, NewCertificates0011.C359, NewCertificates0011.C360, NewCertificates0011.C361, NewCertificates0011.C362, NewCertificates0011.C363, NewCertificates0011.C364, NewCertificates0011.C365, NewCertificates0011.C366, NewCertificates0011.C367, NewCertificates0011.C368, NewCertificates0011.C369, NewCertificates0011.C370, NewCertificates0011.C371, NewCertificates0011.C372, NewCertificates0011.C373, NewCertificates0011.C374, NewCertificates0011.C375, NewCertificates0011.C376, NewCertificates0011.C377, NewCertificates0011.C378, NewCertificates0011.C379, NewCertificates0011.C380, NewCertificates0011.C381, NewCertificates0011.C382, NewCertificates0011.C383} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0011.obstruction352
  · exact NewCertificates0011.obstruction353
  · exact NewCertificates0011.obstruction354
  · exact NewCertificates0011.obstruction355
  · exact NewCertificates0011.obstruction356
  · exact NewCertificates0011.obstruction357
  · exact NewCertificates0011.obstruction358
  · exact NewCertificates0011.obstruction359
  · exact NewCertificates0011.obstruction360
  · exact NewCertificates0011.obstruction361
  · exact NewCertificates0011.obstruction362
  · exact NewCertificates0011.obstruction363
  · exact NewCertificates0011.obstruction364
  · exact NewCertificates0011.obstruction365
  · exact NewCertificates0011.obstruction366
  · exact NewCertificates0011.obstruction367
  · exact NewCertificates0011.obstruction368
  · exact NewCertificates0011.obstruction369
  · exact NewCertificates0011.obstruction370
  · exact NewCertificates0011.obstruction371
  · exact NewCertificates0011.obstruction372
  · exact NewCertificates0011.obstruction373
  · exact NewCertificates0011.obstruction374
  · exact NewCertificates0011.obstruction375
  · exact NewCertificates0011.obstruction376
  · exact NewCertificates0011.obstruction377
  · exact NewCertificates0011.obstruction378
  · exact NewCertificates0011.obstruction379
  · exact NewCertificates0011.obstruction380
  · exact NewCertificates0011.obstruction381
  · exact NewCertificates0011.obstruction382
  · exact NewCertificates0011.obstruction383
end Nut8.FiniteSupport007
