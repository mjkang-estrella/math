import SupportData006
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport006
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0010.C320, NewCertificates0010.C321, NewCertificates0010.C322, NewCertificates0010.C323, NewCertificates0010.C324, NewCertificates0010.C325, NewCertificates0010.C326, NewCertificates0010.C327, NewCertificates0010.C328, NewCertificates0010.C329, NewCertificates0010.C330, NewCertificates0010.C331, NewCertificates0010.C332, NewCertificates0010.C333, NewCertificates0010.C334, NewCertificates0010.C335, NewCertificates0010.C336, NewCertificates0010.C337, NewCertificates0010.C338, NewCertificates0010.C339, NewCertificates0010.C340, NewCertificates0010.C341, NewCertificates0010.C342, NewCertificates0010.C343, NewCertificates0010.C344, NewCertificates0010.C345, NewCertificates0010.C346, NewCertificates0010.C347, NewCertificates0010.C348, NewCertificates0010.C349, NewCertificates0010.C350, NewCertificates0010.C351} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0010.obstruction320
  · exact NewCertificates0010.obstruction321
  · exact NewCertificates0010.obstruction322
  · exact NewCertificates0010.obstruction323
  · exact NewCertificates0010.obstruction324
  · exact NewCertificates0010.obstruction325
  · exact NewCertificates0010.obstruction326
  · exact NewCertificates0010.obstruction327
  · exact NewCertificates0010.obstruction328
  · exact NewCertificates0010.obstruction329
  · exact NewCertificates0010.obstruction330
  · exact NewCertificates0010.obstruction331
  · exact NewCertificates0010.obstruction332
  · exact NewCertificates0010.obstruction333
  · exact NewCertificates0010.obstruction334
  · exact NewCertificates0010.obstruction335
  · exact NewCertificates0010.obstruction336
  · exact NewCertificates0010.obstruction337
  · exact NewCertificates0010.obstruction338
  · exact NewCertificates0010.obstruction339
  · exact NewCertificates0010.obstruction340
  · exact NewCertificates0010.obstruction341
  · exact NewCertificates0010.obstruction342
  · exact NewCertificates0010.obstruction343
  · exact NewCertificates0010.obstruction344
  · exact NewCertificates0010.obstruction345
  · exact NewCertificates0010.obstruction346
  · exact NewCertificates0010.obstruction347
  · exact NewCertificates0010.obstruction348
  · exact NewCertificates0010.obstruction349
  · exact NewCertificates0010.obstruction350
  · exact NewCertificates0010.obstruction351
end Nut8.FiniteSupport006
