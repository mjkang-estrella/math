import SupportData095
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport095
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0137.C4398, NewCertificates0137.C4399, NewCertificates0137.C4400, NewCertificates0137.C4401, NewCertificates0137.C4402, NewCertificates0137.C4403, NewCertificates0137.C4404, NewCertificates0137.C4405, NewCertificates0137.C4406, NewCertificates0137.C4407, NewCertificates0137.C4408, NewCertificates0137.C4409, NewCertificates0137.C4410, NewCertificates0137.C4411, NewCertificates0137.C4412, NewCertificates0137.C4413, NewCertificates0137.C4414, NewCertificates0137.C4415, NewCertificates0138.C4416, NewCertificates0138.C4417, NewCertificates0138.C4418, NewCertificates0138.C4419, NewCertificates0138.C4420, NewCertificates0138.C4421, NewCertificates0138.C4422, NewCertificates0138.C4423, NewCertificates0138.C4424, NewCertificates0138.C4425, NewCertificates0138.C4426, NewCertificates0138.C4427, NewCertificates0138.C4428, NewCertificates0138.C4429} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0138.C4430, NewCertificates0138.C4431, NewCertificates0138.C4432, NewCertificates0138.C4433, NewCertificates0138.C4434, NewCertificates0138.C4435, NewCertificates0138.C4436, NewCertificates0138.C4437, NewCertificates0138.C4438, NewCertificates0138.C4439, NewCertificates0138.C4440, NewCertificates0138.C4441, NewCertificates0138.C4442, NewCertificates0138.C4443, NewCertificates0138.C4444, NewCertificates0138.C4445} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0137.obstruction4398
  · exact NewCertificates0137.obstruction4399
  · exact NewCertificates0137.obstruction4400
  · exact NewCertificates0137.obstruction4401
  · exact NewCertificates0137.obstruction4402
  · exact NewCertificates0137.obstruction4403
  · exact NewCertificates0137.obstruction4404
  · exact NewCertificates0137.obstruction4405
  · exact NewCertificates0137.obstruction4406
  · exact NewCertificates0137.obstruction4407
  · exact NewCertificates0137.obstruction4408
  · exact NewCertificates0137.obstruction4409
  · exact NewCertificates0137.obstruction4410
  · exact NewCertificates0137.obstruction4411
  · exact NewCertificates0137.obstruction4412
  · exact NewCertificates0137.obstruction4413
  · exact NewCertificates0137.obstruction4414
  · exact NewCertificates0137.obstruction4415
  · exact NewCertificates0138.obstruction4416
  · exact NewCertificates0138.obstruction4417
  · exact NewCertificates0138.obstruction4418
  · exact NewCertificates0138.obstruction4419
  · exact NewCertificates0138.obstruction4420
  · exact NewCertificates0138.obstruction4421
  · exact NewCertificates0138.obstruction4422
  · exact NewCertificates0138.obstruction4423
  · exact NewCertificates0138.obstruction4424
  · exact NewCertificates0138.obstruction4425
  · exact NewCertificates0138.obstruction4426
  · exact NewCertificates0138.obstruction4427
  · exact NewCertificates0138.obstruction4428
  · exact NewCertificates0138.obstruction4429
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0138.obstruction4430
  · exact NewCertificates0138.obstruction4431
  · exact NewCertificates0138.obstruction4432
  · exact NewCertificates0138.obstruction4433
  · exact NewCertificates0138.obstruction4434
  · exact NewCertificates0138.obstruction4435
  · exact NewCertificates0138.obstruction4436
  · exact NewCertificates0138.obstruction4437
  · exact NewCertificates0138.obstruction4438
  · exact NewCertificates0138.obstruction4439
  · exact NewCertificates0138.obstruction4440
  · exact NewCertificates0138.obstruction4441
  · exact NewCertificates0138.obstruction4442
  · exact NewCertificates0138.obstruction4443
  · exact NewCertificates0138.obstruction4444
  · exact NewCertificates0138.obstruction4445
end Nut8.FiniteSupport095
