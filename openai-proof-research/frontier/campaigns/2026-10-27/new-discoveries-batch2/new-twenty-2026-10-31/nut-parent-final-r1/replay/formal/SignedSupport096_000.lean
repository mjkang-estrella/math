import SupportData096
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport096
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0138.C4446, NewCertificates0138.C4447, NewCertificates0139.C4448, NewCertificates0139.C4449, NewCertificates0139.C4450, NewCertificates0139.C4451, NewCertificates0139.C4452, NewCertificates0139.C4453, NewCertificates0139.C4454, NewCertificates0139.C4455, NewCertificates0139.C4456, NewCertificates0139.C4457, NewCertificates0139.C4458, NewCertificates0139.C4459, NewCertificates0139.C4460, NewCertificates0139.C4461, NewCertificates0139.C4462, NewCertificates0139.C4463, NewCertificates0139.C4464, NewCertificates0139.C4465, NewCertificates0139.C4466, NewCertificates0139.C4467, NewCertificates0139.C4468, NewCertificates0139.C4469, NewCertificates0139.C4470, NewCertificates0139.C4471, NewCertificates0139.C4472, NewCertificates0139.C4473, NewCertificates0139.C4474, NewCertificates0139.C4475, NewCertificates0139.C4476, NewCertificates0139.C4477} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0139.C4478, NewCertificates0139.C4479, NewCertificates0140.C4480, NewCertificates0140.C4481, NewCertificates0140.C4482, NewCertificates0140.C4483, NewCertificates0140.C4484, NewCertificates0140.C4485, NewCertificates0140.C4486, NewCertificates0140.C4487, NewCertificates0140.C4488, NewCertificates0140.C4489, NewCertificates0140.C4490, NewCertificates0140.C4491, NewCertificates0140.C4492, NewCertificates0140.C4493} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0138.obstruction4446
  · exact NewCertificates0138.obstruction4447
  · exact NewCertificates0139.obstruction4448
  · exact NewCertificates0139.obstruction4449
  · exact NewCertificates0139.obstruction4450
  · exact NewCertificates0139.obstruction4451
  · exact NewCertificates0139.obstruction4452
  · exact NewCertificates0139.obstruction4453
  · exact NewCertificates0139.obstruction4454
  · exact NewCertificates0139.obstruction4455
  · exact NewCertificates0139.obstruction4456
  · exact NewCertificates0139.obstruction4457
  · exact NewCertificates0139.obstruction4458
  · exact NewCertificates0139.obstruction4459
  · exact NewCertificates0139.obstruction4460
  · exact NewCertificates0139.obstruction4461
  · exact NewCertificates0139.obstruction4462
  · exact NewCertificates0139.obstruction4463
  · exact NewCertificates0139.obstruction4464
  · exact NewCertificates0139.obstruction4465
  · exact NewCertificates0139.obstruction4466
  · exact NewCertificates0139.obstruction4467
  · exact NewCertificates0139.obstruction4468
  · exact NewCertificates0139.obstruction4469
  · exact NewCertificates0139.obstruction4470
  · exact NewCertificates0139.obstruction4471
  · exact NewCertificates0139.obstruction4472
  · exact NewCertificates0139.obstruction4473
  · exact NewCertificates0139.obstruction4474
  · exact NewCertificates0139.obstruction4475
  · exact NewCertificates0139.obstruction4476
  · exact NewCertificates0139.obstruction4477
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0139.obstruction4478
  · exact NewCertificates0139.obstruction4479
  · exact NewCertificates0140.obstruction4480
  · exact NewCertificates0140.obstruction4481
  · exact NewCertificates0140.obstruction4482
  · exact NewCertificates0140.obstruction4483
  · exact NewCertificates0140.obstruction4484
  · exact NewCertificates0140.obstruction4485
  · exact NewCertificates0140.obstruction4486
  · exact NewCertificates0140.obstruction4487
  · exact NewCertificates0140.obstruction4488
  · exact NewCertificates0140.obstruction4489
  · exact NewCertificates0140.obstruction4490
  · exact NewCertificates0140.obstruction4491
  · exact NewCertificates0140.obstruction4492
  · exact NewCertificates0140.obstruction4493
end Nut8.FiniteSupport096
