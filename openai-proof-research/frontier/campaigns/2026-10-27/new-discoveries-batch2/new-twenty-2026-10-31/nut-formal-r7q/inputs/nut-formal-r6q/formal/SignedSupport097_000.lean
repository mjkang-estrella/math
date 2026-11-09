import SupportData097
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport097
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0140.C4494, NewCertificates0140.C4495, NewCertificates0140.C4496, NewCertificates0140.C4497, NewCertificates0140.C4498, NewCertificates0140.C4499, NewCertificates0140.C4500, NewCertificates0140.C4501, NewCertificates0140.C4502, NewCertificates0140.C4503, NewCertificates0140.C4504, NewCertificates0140.C4505, NewCertificates0140.C4506, NewCertificates0140.C4507, NewCertificates0140.C4508, NewCertificates0140.C4509, NewCertificates0140.C4510, NewCertificates0140.C4511, NewCertificates0141.C4512, NewCertificates0141.C4513, NewCertificates0141.C4514, NewCertificates0141.C4515, NewCertificates0141.C4516, NewCertificates0141.C4517, NewCertificates0141.C4518, NewCertificates0141.C4519, NewCertificates0141.C4520, NewCertificates0141.C4521, NewCertificates0141.C4522, NewCertificates0141.C4523, NewCertificates0141.C4524, NewCertificates0141.C4525} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0141.C4526, NewCertificates0141.C4527, NewCertificates0141.C4528, NewCertificates0141.C4529, NewCertificates0141.C4530, NewCertificates0141.C4531, NewCertificates0141.C4532, NewCertificates0141.C4533, NewCertificates0141.C4534, NewCertificates0141.C4535, NewCertificates0141.C4536, NewCertificates0141.C4537, NewCertificates0141.C4538, NewCertificates0141.C4539, NewCertificates0141.C4540, NewCertificates0141.C4541} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0140.obstruction4494
  · exact NewCertificates0140.obstruction4495
  · exact NewCertificates0140.obstruction4496
  · exact NewCertificates0140.obstruction4497
  · exact NewCertificates0140.obstruction4498
  · exact NewCertificates0140.obstruction4499
  · exact NewCertificates0140.obstruction4500
  · exact NewCertificates0140.obstruction4501
  · exact NewCertificates0140.obstruction4502
  · exact NewCertificates0140.obstruction4503
  · exact NewCertificates0140.obstruction4504
  · exact NewCertificates0140.obstruction4505
  · exact NewCertificates0140.obstruction4506
  · exact NewCertificates0140.obstruction4507
  · exact NewCertificates0140.obstruction4508
  · exact NewCertificates0140.obstruction4509
  · exact NewCertificates0140.obstruction4510
  · exact NewCertificates0140.obstruction4511
  · exact NewCertificates0141.obstruction4512
  · exact NewCertificates0141.obstruction4513
  · exact NewCertificates0141.obstruction4514
  · exact NewCertificates0141.obstruction4515
  · exact NewCertificates0141.obstruction4516
  · exact NewCertificates0141.obstruction4517
  · exact NewCertificates0141.obstruction4518
  · exact NewCertificates0141.obstruction4519
  · exact NewCertificates0141.obstruction4520
  · exact NewCertificates0141.obstruction4521
  · exact NewCertificates0141.obstruction4522
  · exact NewCertificates0141.obstruction4523
  · exact NewCertificates0141.obstruction4524
  · exact NewCertificates0141.obstruction4525
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0141.obstruction4526
  · exact NewCertificates0141.obstruction4527
  · exact NewCertificates0141.obstruction4528
  · exact NewCertificates0141.obstruction4529
  · exact NewCertificates0141.obstruction4530
  · exact NewCertificates0141.obstruction4531
  · exact NewCertificates0141.obstruction4532
  · exact NewCertificates0141.obstruction4533
  · exact NewCertificates0141.obstruction4534
  · exact NewCertificates0141.obstruction4535
  · exact NewCertificates0141.obstruction4536
  · exact NewCertificates0141.obstruction4537
  · exact NewCertificates0141.obstruction4538
  · exact NewCertificates0141.obstruction4539
  · exact NewCertificates0141.obstruction4540
  · exact NewCertificates0141.obstruction4541
end Nut8.FiniteSupport097
