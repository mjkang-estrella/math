import SupportData098
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport098
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0141.C4542, NewCertificates0141.C4543, NewCertificates0142.C4544, NewCertificates0142.C4545, NewCertificates0142.C4546, NewCertificates0142.C4547, NewCertificates0142.C4548, NewCertificates0142.C4549, NewCertificates0142.C4550, NewCertificates0142.C4551, NewCertificates0142.C4552, NewCertificates0142.C4553, NewCertificates0142.C4554, NewCertificates0142.C4555, NewCertificates0142.C4556, NewCertificates0142.C4557, NewCertificates0142.C4558, NewCertificates0142.C4559, NewCertificates0142.C4560, NewCertificates0142.C4561, NewCertificates0142.C4562, NewCertificates0142.C4563, NewCertificates0142.C4564, NewCertificates0142.C4565, NewCertificates0142.C4566, NewCertificates0142.C4567, NewCertificates0142.C4568, NewCertificates0142.C4569, NewCertificates0142.C4570, NewCertificates0142.C4571, NewCertificates0142.C4572, NewCertificates0142.C4573} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0142.C4574, NewCertificates0142.C4575, NewCertificates0143.C4576, NewCertificates0143.C4577, NewCertificates0143.C4578, NewCertificates0143.C4579, NewCertificates0143.C4580, NewCertificates0143.C4581, NewCertificates0143.C4582, NewCertificates0143.C4583, NewCertificates0143.C4584, NewCertificates0143.C4585, NewCertificates0143.C4586, NewCertificates0143.C4587, NewCertificates0143.C4588, NewCertificates0143.C4589} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0141.obstruction4542
  · exact NewCertificates0141.obstruction4543
  · exact NewCertificates0142.obstruction4544
  · exact NewCertificates0142.obstruction4545
  · exact NewCertificates0142.obstruction4546
  · exact NewCertificates0142.obstruction4547
  · exact NewCertificates0142.obstruction4548
  · exact NewCertificates0142.obstruction4549
  · exact NewCertificates0142.obstruction4550
  · exact NewCertificates0142.obstruction4551
  · exact NewCertificates0142.obstruction4552
  · exact NewCertificates0142.obstruction4553
  · exact NewCertificates0142.obstruction4554
  · exact NewCertificates0142.obstruction4555
  · exact NewCertificates0142.obstruction4556
  · exact NewCertificates0142.obstruction4557
  · exact NewCertificates0142.obstruction4558
  · exact NewCertificates0142.obstruction4559
  · exact NewCertificates0142.obstruction4560
  · exact NewCertificates0142.obstruction4561
  · exact NewCertificates0142.obstruction4562
  · exact NewCertificates0142.obstruction4563
  · exact NewCertificates0142.obstruction4564
  · exact NewCertificates0142.obstruction4565
  · exact NewCertificates0142.obstruction4566
  · exact NewCertificates0142.obstruction4567
  · exact NewCertificates0142.obstruction4568
  · exact NewCertificates0142.obstruction4569
  · exact NewCertificates0142.obstruction4570
  · exact NewCertificates0142.obstruction4571
  · exact NewCertificates0142.obstruction4572
  · exact NewCertificates0142.obstruction4573
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0142.obstruction4574
  · exact NewCertificates0142.obstruction4575
  · exact NewCertificates0143.obstruction4576
  · exact NewCertificates0143.obstruction4577
  · exact NewCertificates0143.obstruction4578
  · exact NewCertificates0143.obstruction4579
  · exact NewCertificates0143.obstruction4580
  · exact NewCertificates0143.obstruction4581
  · exact NewCertificates0143.obstruction4582
  · exact NewCertificates0143.obstruction4583
  · exact NewCertificates0143.obstruction4584
  · exact NewCertificates0143.obstruction4585
  · exact NewCertificates0143.obstruction4586
  · exact NewCertificates0143.obstruction4587
  · exact NewCertificates0143.obstruction4588
  · exact NewCertificates0143.obstruction4589
end Nut8.FiniteSupport098
