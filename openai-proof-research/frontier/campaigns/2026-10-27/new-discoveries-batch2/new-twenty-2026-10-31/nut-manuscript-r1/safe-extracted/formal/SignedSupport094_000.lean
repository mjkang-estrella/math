import SupportData094
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport094
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0135.C4326, NewCertificates0135.C4327, NewCertificates0135.C4328, NewCertificates0135.C4329, NewCertificates0135.C4330, NewCertificates0135.C4331, NewCertificates0135.C4332, NewCertificates0135.C4333, NewCertificates0135.C4334, NewCertificates0135.C4335, NewCertificates0135.C4336, NewCertificates0135.C4337, NewCertificates0135.C4338, NewCertificates0135.C4339, NewCertificates0135.C4340, NewCertificates0135.C4341} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0135.C4342, NewCertificates0135.C4343, NewCertificates0135.C4344, NewCertificates0135.C4345, NewCertificates0135.C4346, NewCertificates0135.C4347, NewCertificates0135.C4348, NewCertificates0135.C4349, NewCertificates0135.C4350, NewCertificates0135.C4351, NewCertificates0136.C4352, NewCertificates0136.C4353, NewCertificates0136.C4354, NewCertificates0136.C4355, NewCertificates0136.C4356, NewCertificates0136.C4357} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0136.C4358, NewCertificates0136.C4359, NewCertificates0136.C4360, NewCertificates0136.C4361, NewCertificates0136.C4362, NewCertificates0136.C4363, NewCertificates0136.C4364, NewCertificates0136.C4365, NewCertificates0136.C4366, NewCertificates0136.C4367, NewCertificates0136.C4368, NewCertificates0136.C4369, NewCertificates0136.C4370, NewCertificates0136.C4371, NewCertificates0136.C4372, NewCertificates0136.C4373} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0136.C4374, NewCertificates0136.C4375, NewCertificates0136.C4376, NewCertificates0136.C4377, NewCertificates0136.C4378, NewCertificates0136.C4379, NewCertificates0136.C4380, NewCertificates0136.C4381, NewCertificates0136.C4382, NewCertificates0136.C4383, NewCertificates0137.C4384, NewCertificates0137.C4385, NewCertificates0137.C4386, NewCertificates0137.C4387, NewCertificates0137.C4388, NewCertificates0137.C4389} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0135.obstruction4326
  · exact NewCertificates0135.obstruction4327
  · exact NewCertificates0135.obstruction4328
  · exact NewCertificates0135.obstruction4329
  · exact NewCertificates0135.obstruction4330
  · exact NewCertificates0135.obstruction4331
  · exact NewCertificates0135.obstruction4332
  · exact NewCertificates0135.obstruction4333
  · exact NewCertificates0135.obstruction4334
  · exact NewCertificates0135.obstruction4335
  · exact NewCertificates0135.obstruction4336
  · exact NewCertificates0135.obstruction4337
  · exact NewCertificates0135.obstruction4338
  · exact NewCertificates0135.obstruction4339
  · exact NewCertificates0135.obstruction4340
  · exact NewCertificates0135.obstruction4341
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0135.obstruction4342
  · exact NewCertificates0135.obstruction4343
  · exact NewCertificates0135.obstruction4344
  · exact NewCertificates0135.obstruction4345
  · exact NewCertificates0135.obstruction4346
  · exact NewCertificates0135.obstruction4347
  · exact NewCertificates0135.obstruction4348
  · exact NewCertificates0135.obstruction4349
  · exact NewCertificates0135.obstruction4350
  · exact NewCertificates0135.obstruction4351
  · exact NewCertificates0136.obstruction4352
  · exact NewCertificates0136.obstruction4353
  · exact NewCertificates0136.obstruction4354
  · exact NewCertificates0136.obstruction4355
  · exact NewCertificates0136.obstruction4356
  · exact NewCertificates0136.obstruction4357
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0136.obstruction4358
  · exact NewCertificates0136.obstruction4359
  · exact NewCertificates0136.obstruction4360
  · exact NewCertificates0136.obstruction4361
  · exact NewCertificates0136.obstruction4362
  · exact NewCertificates0136.obstruction4363
  · exact NewCertificates0136.obstruction4364
  · exact NewCertificates0136.obstruction4365
  · exact NewCertificates0136.obstruction4366
  · exact NewCertificates0136.obstruction4367
  · exact NewCertificates0136.obstruction4368
  · exact NewCertificates0136.obstruction4369
  · exact NewCertificates0136.obstruction4370
  · exact NewCertificates0136.obstruction4371
  · exact NewCertificates0136.obstruction4372
  · exact NewCertificates0136.obstruction4373
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0136.obstruction4374
  · exact NewCertificates0136.obstruction4375
  · exact NewCertificates0136.obstruction4376
  · exact NewCertificates0136.obstruction4377
  · exact NewCertificates0136.obstruction4378
  · exact NewCertificates0136.obstruction4379
  · exact NewCertificates0136.obstruction4380
  · exact NewCertificates0136.obstruction4381
  · exact NewCertificates0136.obstruction4382
  · exact NewCertificates0136.obstruction4383
  · exact NewCertificates0137.obstruction4384
  · exact NewCertificates0137.obstruction4385
  · exact NewCertificates0137.obstruction4386
  · exact NewCertificates0137.obstruction4387
  · exact NewCertificates0137.obstruction4388
  · exact NewCertificates0137.obstruction4389
end Nut8.FiniteSupport094
