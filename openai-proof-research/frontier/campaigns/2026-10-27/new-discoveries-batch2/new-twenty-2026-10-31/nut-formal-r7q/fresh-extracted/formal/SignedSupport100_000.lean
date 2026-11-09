import SupportData100
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport100
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0144.C4638, NewCertificates0144.C4639, NewCertificates0145.C4640, NewCertificates0145.C4641, NewCertificates0145.C4642, NewCertificates0145.C4643, NewCertificates0145.C4644, NewCertificates0145.C4645, NewCertificates0145.C4646, NewCertificates0145.C4647, NewCertificates0145.C4648, NewCertificates0145.C4649, NewCertificates0145.C4650, NewCertificates0145.C4651, NewCertificates0145.C4652, NewCertificates0145.C4653, NewCertificates0145.C4654, NewCertificates0145.C4655, NewCertificates0145.C4656, NewCertificates0145.C4657, NewCertificates0145.C4658, NewCertificates0145.C4659, NewCertificates0145.C4660, NewCertificates0145.C4661, NewCertificates0145.C4662, NewCertificates0145.C4663, NewCertificates0145.C4664, NewCertificates0145.C4665, NewCertificates0145.C4666, NewCertificates0145.C4667, NewCertificates0145.C4668, NewCertificates0145.C4669} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0145.C4670, NewCertificates0145.C4671, NewCertificates0146.C4672, NewCertificates0146.C4673, NewCertificates0146.C4674, NewCertificates0146.C4675, NewCertificates0146.C4676, NewCertificates0146.C4677, NewCertificates0146.C4678, NewCertificates0146.C4679, NewCertificates0146.C4680, NewCertificates0146.C4681, NewCertificates0146.C4682, NewCertificates0146.C4683, NewCertificates0146.C4684, NewCertificates0146.C4685} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0146.C4686, NewCertificates0146.C4687, NewCertificates0146.C4688, NewCertificates0146.C4689, NewCertificates0146.C4690, NewCertificates0146.C4691, NewCertificates0146.C4692, NewCertificates0146.C4693, NewCertificates0146.C4694, NewCertificates0146.C4695, NewCertificates0146.C4696, NewCertificates0146.C4697, NewCertificates0146.C4698, NewCertificates0146.C4699, NewCertificates0146.C4700, NewCertificates0146.C4701} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0144.obstruction4638
  · exact NewCertificates0144.obstruction4639
  · exact NewCertificates0145.obstruction4640
  · exact NewCertificates0145.obstruction4641
  · exact NewCertificates0145.obstruction4642
  · exact NewCertificates0145.obstruction4643
  · exact NewCertificates0145.obstruction4644
  · exact NewCertificates0145.obstruction4645
  · exact NewCertificates0145.obstruction4646
  · exact NewCertificates0145.obstruction4647
  · exact NewCertificates0145.obstruction4648
  · exact NewCertificates0145.obstruction4649
  · exact NewCertificates0145.obstruction4650
  · exact NewCertificates0145.obstruction4651
  · exact NewCertificates0145.obstruction4652
  · exact NewCertificates0145.obstruction4653
  · exact NewCertificates0145.obstruction4654
  · exact NewCertificates0145.obstruction4655
  · exact NewCertificates0145.obstruction4656
  · exact NewCertificates0145.obstruction4657
  · exact NewCertificates0145.obstruction4658
  · exact NewCertificates0145.obstruction4659
  · exact NewCertificates0145.obstruction4660
  · exact NewCertificates0145.obstruction4661
  · exact NewCertificates0145.obstruction4662
  · exact NewCertificates0145.obstruction4663
  · exact NewCertificates0145.obstruction4664
  · exact NewCertificates0145.obstruction4665
  · exact NewCertificates0145.obstruction4666
  · exact NewCertificates0145.obstruction4667
  · exact NewCertificates0145.obstruction4668
  · exact NewCertificates0145.obstruction4669
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0145.obstruction4670
  · exact NewCertificates0145.obstruction4671
  · exact NewCertificates0146.obstruction4672
  · exact NewCertificates0146.obstruction4673
  · exact NewCertificates0146.obstruction4674
  · exact NewCertificates0146.obstruction4675
  · exact NewCertificates0146.obstruction4676
  · exact NewCertificates0146.obstruction4677
  · exact NewCertificates0146.obstruction4678
  · exact NewCertificates0146.obstruction4679
  · exact NewCertificates0146.obstruction4680
  · exact NewCertificates0146.obstruction4681
  · exact NewCertificates0146.obstruction4682
  · exact NewCertificates0146.obstruction4683
  · exact NewCertificates0146.obstruction4684
  · exact NewCertificates0146.obstruction4685
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0146.obstruction4686
  · exact NewCertificates0146.obstruction4687
  · exact NewCertificates0146.obstruction4688
  · exact NewCertificates0146.obstruction4689
  · exact NewCertificates0146.obstruction4690
  · exact NewCertificates0146.obstruction4691
  · exact NewCertificates0146.obstruction4692
  · exact NewCertificates0146.obstruction4693
  · exact NewCertificates0146.obstruction4694
  · exact NewCertificates0146.obstruction4695
  · exact NewCertificates0146.obstruction4696
  · exact NewCertificates0146.obstruction4697
  · exact NewCertificates0146.obstruction4698
  · exact NewCertificates0146.obstruction4699
  · exact NewCertificates0146.obstruction4700
  · exact NewCertificates0146.obstruction4701
end Nut8.FiniteSupport100
