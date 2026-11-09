import SupportData093
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport093
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0134.C4294, NewCertificates0134.C4295, NewCertificates0134.C4296, NewCertificates0134.C4297, NewCertificates0134.C4298, NewCertificates0134.C4299, NewCertificates0134.C4300, NewCertificates0134.C4301, NewCertificates0134.C4302, NewCertificates0134.C4303, NewCertificates0134.C4304, NewCertificates0134.C4305, NewCertificates0134.C4306, NewCertificates0134.C4307, NewCertificates0134.C4308, NewCertificates0134.C4309, NewCertificates0134.C4310, NewCertificates0134.C4311, NewCertificates0134.C4312, NewCertificates0134.C4313, NewCertificates0134.C4314, NewCertificates0134.C4315, NewCertificates0134.C4316, NewCertificates0134.C4317, NewCertificates0134.C4318, NewCertificates0134.C4319, NewCertificates0135.C4320, NewCertificates0135.C4321, NewCertificates0135.C4322, NewCertificates0135.C4323, NewCertificates0135.C4324, NewCertificates0135.C4325} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0134.obstruction4294
  · exact NewCertificates0134.obstruction4295
  · exact NewCertificates0134.obstruction4296
  · exact NewCertificates0134.obstruction4297
  · exact NewCertificates0134.obstruction4298
  · exact NewCertificates0134.obstruction4299
  · exact NewCertificates0134.obstruction4300
  · exact NewCertificates0134.obstruction4301
  · exact NewCertificates0134.obstruction4302
  · exact NewCertificates0134.obstruction4303
  · exact NewCertificates0134.obstruction4304
  · exact NewCertificates0134.obstruction4305
  · exact NewCertificates0134.obstruction4306
  · exact NewCertificates0134.obstruction4307
  · exact NewCertificates0134.obstruction4308
  · exact NewCertificates0134.obstruction4309
  · exact NewCertificates0134.obstruction4310
  · exact NewCertificates0134.obstruction4311
  · exact NewCertificates0134.obstruction4312
  · exact NewCertificates0134.obstruction4313
  · exact NewCertificates0134.obstruction4314
  · exact NewCertificates0134.obstruction4315
  · exact NewCertificates0134.obstruction4316
  · exact NewCertificates0134.obstruction4317
  · exact NewCertificates0134.obstruction4318
  · exact NewCertificates0134.obstruction4319
  · exact NewCertificates0135.obstruction4320
  · exact NewCertificates0135.obstruction4321
  · exact NewCertificates0135.obstruction4322
  · exact NewCertificates0135.obstruction4323
  · exact NewCertificates0135.obstruction4324
  · exact NewCertificates0135.obstruction4325
end Nut8.FiniteSupport093
