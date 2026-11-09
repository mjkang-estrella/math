import SupportData099
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport099
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0143.C4590, NewCertificates0143.C4591, NewCertificates0143.C4592, NewCertificates0143.C4593, NewCertificates0143.C4594, NewCertificates0143.C4595, NewCertificates0143.C4596, NewCertificates0143.C4597, NewCertificates0143.C4598, NewCertificates0143.C4599, NewCertificates0143.C4600, NewCertificates0143.C4601, NewCertificates0143.C4602, NewCertificates0143.C4603, NewCertificates0143.C4604, NewCertificates0143.C4605, NewCertificates0143.C4606, NewCertificates0143.C4607, NewCertificates0144.C4608, NewCertificates0144.C4609, NewCertificates0144.C4610, NewCertificates0144.C4611, NewCertificates0144.C4612, NewCertificates0144.C4613, NewCertificates0144.C4614, NewCertificates0144.C4615, NewCertificates0144.C4616, NewCertificates0144.C4617, NewCertificates0144.C4618, NewCertificates0144.C4619, NewCertificates0144.C4620, NewCertificates0144.C4621} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0144.C4622, NewCertificates0144.C4623, NewCertificates0144.C4624, NewCertificates0144.C4625, NewCertificates0144.C4626, NewCertificates0144.C4627, NewCertificates0144.C4628, NewCertificates0144.C4629, NewCertificates0144.C4630, NewCertificates0144.C4631, NewCertificates0144.C4632, NewCertificates0144.C4633, NewCertificates0144.C4634, NewCertificates0144.C4635, NewCertificates0144.C4636, NewCertificates0144.C4637} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0143.obstruction4590
  · exact NewCertificates0143.obstruction4591
  · exact NewCertificates0143.obstruction4592
  · exact NewCertificates0143.obstruction4593
  · exact NewCertificates0143.obstruction4594
  · exact NewCertificates0143.obstruction4595
  · exact NewCertificates0143.obstruction4596
  · exact NewCertificates0143.obstruction4597
  · exact NewCertificates0143.obstruction4598
  · exact NewCertificates0143.obstruction4599
  · exact NewCertificates0143.obstruction4600
  · exact NewCertificates0143.obstruction4601
  · exact NewCertificates0143.obstruction4602
  · exact NewCertificates0143.obstruction4603
  · exact NewCertificates0143.obstruction4604
  · exact NewCertificates0143.obstruction4605
  · exact NewCertificates0143.obstruction4606
  · exact NewCertificates0143.obstruction4607
  · exact NewCertificates0144.obstruction4608
  · exact NewCertificates0144.obstruction4609
  · exact NewCertificates0144.obstruction4610
  · exact NewCertificates0144.obstruction4611
  · exact NewCertificates0144.obstruction4612
  · exact NewCertificates0144.obstruction4613
  · exact NewCertificates0144.obstruction4614
  · exact NewCertificates0144.obstruction4615
  · exact NewCertificates0144.obstruction4616
  · exact NewCertificates0144.obstruction4617
  · exact NewCertificates0144.obstruction4618
  · exact NewCertificates0144.obstruction4619
  · exact NewCertificates0144.obstruction4620
  · exact NewCertificates0144.obstruction4621
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0144.obstruction4622
  · exact NewCertificates0144.obstruction4623
  · exact NewCertificates0144.obstruction4624
  · exact NewCertificates0144.obstruction4625
  · exact NewCertificates0144.obstruction4626
  · exact NewCertificates0144.obstruction4627
  · exact NewCertificates0144.obstruction4628
  · exact NewCertificates0144.obstruction4629
  · exact NewCertificates0144.obstruction4630
  · exact NewCertificates0144.obstruction4631
  · exact NewCertificates0144.obstruction4632
  · exact NewCertificates0144.obstruction4633
  · exact NewCertificates0144.obstruction4634
  · exact NewCertificates0144.obstruction4635
  · exact NewCertificates0144.obstruction4636
  · exact NewCertificates0144.obstruction4637
end Nut8.FiniteSupport099
