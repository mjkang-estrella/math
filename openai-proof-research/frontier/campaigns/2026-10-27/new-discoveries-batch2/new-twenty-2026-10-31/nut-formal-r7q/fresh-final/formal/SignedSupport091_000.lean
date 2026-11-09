import SupportData091
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport091
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0131.C4206, NewCertificates0131.C4207, NewCertificates0131.C4208, NewCertificates0131.C4209, NewCertificates0131.C4210, NewCertificates0131.C4211, NewCertificates0131.C4212, NewCertificates0131.C4213, NewCertificates0131.C4214, NewCertificates0131.C4215, NewCertificates0131.C4216, NewCertificates0131.C4217, NewCertificates0131.C4218, NewCertificates0131.C4219, NewCertificates0131.C4220, NewCertificates0131.C4221, NewCertificates0131.C4222, NewCertificates0131.C4223, NewCertificates0132.C4224, NewCertificates0132.C4225, NewCertificates0132.C4226, NewCertificates0132.C4227, NewCertificates0132.C4228, NewCertificates0132.C4229, NewCertificates0132.C4230, NewCertificates0132.C4231, NewCertificates0132.C4232, NewCertificates0132.C4233, NewCertificates0132.C4234, NewCertificates0132.C4235, NewCertificates0132.C4236, NewCertificates0132.C4237} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0131.obstruction4206
  · exact NewCertificates0131.obstruction4207
  · exact NewCertificates0131.obstruction4208
  · exact NewCertificates0131.obstruction4209
  · exact NewCertificates0131.obstruction4210
  · exact NewCertificates0131.obstruction4211
  · exact NewCertificates0131.obstruction4212
  · exact NewCertificates0131.obstruction4213
  · exact NewCertificates0131.obstruction4214
  · exact NewCertificates0131.obstruction4215
  · exact NewCertificates0131.obstruction4216
  · exact NewCertificates0131.obstruction4217
  · exact NewCertificates0131.obstruction4218
  · exact NewCertificates0131.obstruction4219
  · exact NewCertificates0131.obstruction4220
  · exact NewCertificates0131.obstruction4221
  · exact NewCertificates0131.obstruction4222
  · exact NewCertificates0131.obstruction4223
  · exact NewCertificates0132.obstruction4224
  · exact NewCertificates0132.obstruction4225
  · exact NewCertificates0132.obstruction4226
  · exact NewCertificates0132.obstruction4227
  · exact NewCertificates0132.obstruction4228
  · exact NewCertificates0132.obstruction4229
  · exact NewCertificates0132.obstruction4230
  · exact NewCertificates0132.obstruction4231
  · exact NewCertificates0132.obstruction4232
  · exact NewCertificates0132.obstruction4233
  · exact NewCertificates0132.obstruction4234
  · exact NewCertificates0132.obstruction4235
  · exact NewCertificates0132.obstruction4236
  · exact NewCertificates0132.obstruction4237
end Nut8.FiniteSupport091
