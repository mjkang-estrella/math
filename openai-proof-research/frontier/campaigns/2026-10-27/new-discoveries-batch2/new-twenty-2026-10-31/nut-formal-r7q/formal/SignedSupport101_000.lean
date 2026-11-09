import SupportData101
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport101
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0146.C4702, NewCertificates0146.C4703, NewCertificates0147.C4704, NewCertificates0147.C4705, NewCertificates0147.C4706, NewCertificates0147.C4707, NewCertificates0147.C4708, NewCertificates0147.C4709, NewCertificates0147.C4710, NewCertificates0147.C4711, NewCertificates0147.C4712, NewCertificates0147.C4713, NewCertificates0147.C4714, NewCertificates0147.C4715, NewCertificates0147.C4716, NewCertificates0147.C4717} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0147.C4718, NewCertificates0147.C4719, NewCertificates0147.C4720, NewCertificates0147.C4721, NewCertificates0147.C4722, NewCertificates0147.C4723, NewCertificates0147.C4724, NewCertificates0147.C4725, NewCertificates0147.C4726, NewCertificates0147.C4727, NewCertificates0147.C4728, NewCertificates0147.C4729, NewCertificates0147.C4730, NewCertificates0147.C4731, NewCertificates0147.C4732, NewCertificates0147.C4733} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0147.C4734, NewCertificates0147.C4735, NewCertificates0148.C4736, NewCertificates0148.C4737, NewCertificates0148.C4738, NewCertificates0148.C4739, NewCertificates0148.C4740, NewCertificates0148.C4741, NewCertificates0148.C4742, NewCertificates0148.C4743, NewCertificates0148.C4744, NewCertificates0148.C4745, NewCertificates0148.C4746, NewCertificates0148.C4747, NewCertificates0148.C4748, NewCertificates0148.C4749} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0148.C4750, NewCertificates0148.C4751, NewCertificates0148.C4752, NewCertificates0148.C4753, NewCertificates0148.C4754, NewCertificates0148.C4755, NewCertificates0148.C4756, NewCertificates0148.C4757} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0146.obstruction4702
  · exact NewCertificates0146.obstruction4703
  · exact NewCertificates0147.obstruction4704
  · exact NewCertificates0147.obstruction4705
  · exact NewCertificates0147.obstruction4706
  · exact NewCertificates0147.obstruction4707
  · exact NewCertificates0147.obstruction4708
  · exact NewCertificates0147.obstruction4709
  · exact NewCertificates0147.obstruction4710
  · exact NewCertificates0147.obstruction4711
  · exact NewCertificates0147.obstruction4712
  · exact NewCertificates0147.obstruction4713
  · exact NewCertificates0147.obstruction4714
  · exact NewCertificates0147.obstruction4715
  · exact NewCertificates0147.obstruction4716
  · exact NewCertificates0147.obstruction4717
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0147.obstruction4718
  · exact NewCertificates0147.obstruction4719
  · exact NewCertificates0147.obstruction4720
  · exact NewCertificates0147.obstruction4721
  · exact NewCertificates0147.obstruction4722
  · exact NewCertificates0147.obstruction4723
  · exact NewCertificates0147.obstruction4724
  · exact NewCertificates0147.obstruction4725
  · exact NewCertificates0147.obstruction4726
  · exact NewCertificates0147.obstruction4727
  · exact NewCertificates0147.obstruction4728
  · exact NewCertificates0147.obstruction4729
  · exact NewCertificates0147.obstruction4730
  · exact NewCertificates0147.obstruction4731
  · exact NewCertificates0147.obstruction4732
  · exact NewCertificates0147.obstruction4733
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0147.obstruction4734
  · exact NewCertificates0147.obstruction4735
  · exact NewCertificates0148.obstruction4736
  · exact NewCertificates0148.obstruction4737
  · exact NewCertificates0148.obstruction4738
  · exact NewCertificates0148.obstruction4739
  · exact NewCertificates0148.obstruction4740
  · exact NewCertificates0148.obstruction4741
  · exact NewCertificates0148.obstruction4742
  · exact NewCertificates0148.obstruction4743
  · exact NewCertificates0148.obstruction4744
  · exact NewCertificates0148.obstruction4745
  · exact NewCertificates0148.obstruction4746
  · exact NewCertificates0148.obstruction4747
  · exact NewCertificates0148.obstruction4748
  · exact NewCertificates0148.obstruction4749
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0148.obstruction4750
  · exact NewCertificates0148.obstruction4751
  · exact NewCertificates0148.obstruction4752
  · exact NewCertificates0148.obstruction4753
  · exact NewCertificates0148.obstruction4754
  · exact NewCertificates0148.obstruction4755
  · exact NewCertificates0148.obstruction4756
  · exact NewCertificates0148.obstruction4757
end Nut8.FiniteSupport101
