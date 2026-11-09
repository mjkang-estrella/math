import SupportData092
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport092
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0132.C4238, NewCertificates0132.C4239, NewCertificates0132.C4240, NewCertificates0132.C4241, NewCertificates0132.C4242, NewCertificates0132.C4243, NewCertificates0132.C4244, NewCertificates0132.C4245, NewCertificates0132.C4246, NewCertificates0132.C4247, NewCertificates0132.C4248, NewCertificates0132.C4249, NewCertificates0132.C4250, NewCertificates0132.C4251, NewCertificates0132.C4252, NewCertificates0132.C4253} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0132.C4254, NewCertificates0132.C4255, NewCertificates0133.C4256, NewCertificates0133.C4257, NewCertificates0133.C4258, NewCertificates0133.C4259, NewCertificates0133.C4260, NewCertificates0133.C4261, NewCertificates0133.C4262, NewCertificates0133.C4263, NewCertificates0133.C4264, NewCertificates0133.C4265, NewCertificates0133.C4266, NewCertificates0133.C4267, NewCertificates0133.C4268, NewCertificates0133.C4269} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0133.C4270, NewCertificates0133.C4271, NewCertificates0133.C4272, NewCertificates0133.C4273, NewCertificates0133.C4274, NewCertificates0133.C4275, NewCertificates0133.C4276, NewCertificates0133.C4277, NewCertificates0133.C4278, NewCertificates0133.C4279, NewCertificates0133.C4280, NewCertificates0133.C4281, NewCertificates0133.C4282, NewCertificates0133.C4283, NewCertificates0133.C4284, NewCertificates0133.C4285} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0133.C4286, NewCertificates0133.C4287, NewCertificates0134.C4288, NewCertificates0134.C4289, NewCertificates0134.C4290, NewCertificates0134.C4291, NewCertificates0134.C4292, NewCertificates0134.C4293} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0132.obstruction4238
  · exact NewCertificates0132.obstruction4239
  · exact NewCertificates0132.obstruction4240
  · exact NewCertificates0132.obstruction4241
  · exact NewCertificates0132.obstruction4242
  · exact NewCertificates0132.obstruction4243
  · exact NewCertificates0132.obstruction4244
  · exact NewCertificates0132.obstruction4245
  · exact NewCertificates0132.obstruction4246
  · exact NewCertificates0132.obstruction4247
  · exact NewCertificates0132.obstruction4248
  · exact NewCertificates0132.obstruction4249
  · exact NewCertificates0132.obstruction4250
  · exact NewCertificates0132.obstruction4251
  · exact NewCertificates0132.obstruction4252
  · exact NewCertificates0132.obstruction4253
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0132.obstruction4254
  · exact NewCertificates0132.obstruction4255
  · exact NewCertificates0133.obstruction4256
  · exact NewCertificates0133.obstruction4257
  · exact NewCertificates0133.obstruction4258
  · exact NewCertificates0133.obstruction4259
  · exact NewCertificates0133.obstruction4260
  · exact NewCertificates0133.obstruction4261
  · exact NewCertificates0133.obstruction4262
  · exact NewCertificates0133.obstruction4263
  · exact NewCertificates0133.obstruction4264
  · exact NewCertificates0133.obstruction4265
  · exact NewCertificates0133.obstruction4266
  · exact NewCertificates0133.obstruction4267
  · exact NewCertificates0133.obstruction4268
  · exact NewCertificates0133.obstruction4269
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0133.obstruction4270
  · exact NewCertificates0133.obstruction4271
  · exact NewCertificates0133.obstruction4272
  · exact NewCertificates0133.obstruction4273
  · exact NewCertificates0133.obstruction4274
  · exact NewCertificates0133.obstruction4275
  · exact NewCertificates0133.obstruction4276
  · exact NewCertificates0133.obstruction4277
  · exact NewCertificates0133.obstruction4278
  · exact NewCertificates0133.obstruction4279
  · exact NewCertificates0133.obstruction4280
  · exact NewCertificates0133.obstruction4281
  · exact NewCertificates0133.obstruction4282
  · exact NewCertificates0133.obstruction4283
  · exact NewCertificates0133.obstruction4284
  · exact NewCertificates0133.obstruction4285
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0133.obstruction4286
  · exact NewCertificates0133.obstruction4287
  · exact NewCertificates0134.obstruction4288
  · exact NewCertificates0134.obstruction4289
  · exact NewCertificates0134.obstruction4290
  · exact NewCertificates0134.obstruction4291
  · exact NewCertificates0134.obstruction4292
  · exact NewCertificates0134.obstruction4293
end Nut8.FiniteSupport092
