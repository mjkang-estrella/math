import SupportData102
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport102
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0148.C4758, NewCertificates0148.C4759, NewCertificates0148.C4760, NewCertificates0148.C4761, NewCertificates0148.C4762, NewCertificates0148.C4763, NewCertificates0148.C4764, NewCertificates0148.C4765, NewCertificates0148.C4766, NewCertificates0148.C4767, NewCertificates0149.C4768, NewCertificates0149.C4769, NewCertificates0149.C4770, NewCertificates0149.C4771, NewCertificates0149.C4772, NewCertificates0149.C4773, NewCertificates0149.C4774, NewCertificates0149.C4775, NewCertificates0149.C4776, NewCertificates0149.C4777, NewCertificates0149.C4778, NewCertificates0149.C4779, NewCertificates0149.C4780, NewCertificates0149.C4781, NewCertificates0149.C4782, NewCertificates0149.C4783, NewCertificates0149.C4784, NewCertificates0149.C4785, NewCertificates0149.C4786, NewCertificates0149.C4787, NewCertificates0149.C4788, NewCertificates0149.C4789} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0149.C4790, NewCertificates0149.C4791, NewCertificates0149.C4792, NewCertificates0149.C4793, NewCertificates0149.C4794, NewCertificates0149.C4795, NewCertificates0149.C4796, NewCertificates0149.C4797, NewCertificates0149.C4798, NewCertificates0149.C4799, NewCertificates0150.C4800, NewCertificates0150.C4801, NewCertificates0150.C4802, NewCertificates0150.C4803, NewCertificates0150.C4804, NewCertificates0150.C4805} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0148.obstruction4758
  · exact NewCertificates0148.obstruction4759
  · exact NewCertificates0148.obstruction4760
  · exact NewCertificates0148.obstruction4761
  · exact NewCertificates0148.obstruction4762
  · exact NewCertificates0148.obstruction4763
  · exact NewCertificates0148.obstruction4764
  · exact NewCertificates0148.obstruction4765
  · exact NewCertificates0148.obstruction4766
  · exact NewCertificates0148.obstruction4767
  · exact NewCertificates0149.obstruction4768
  · exact NewCertificates0149.obstruction4769
  · exact NewCertificates0149.obstruction4770
  · exact NewCertificates0149.obstruction4771
  · exact NewCertificates0149.obstruction4772
  · exact NewCertificates0149.obstruction4773
  · exact NewCertificates0149.obstruction4774
  · exact NewCertificates0149.obstruction4775
  · exact NewCertificates0149.obstruction4776
  · exact NewCertificates0149.obstruction4777
  · exact NewCertificates0149.obstruction4778
  · exact NewCertificates0149.obstruction4779
  · exact NewCertificates0149.obstruction4780
  · exact NewCertificates0149.obstruction4781
  · exact NewCertificates0149.obstruction4782
  · exact NewCertificates0149.obstruction4783
  · exact NewCertificates0149.obstruction4784
  · exact NewCertificates0149.obstruction4785
  · exact NewCertificates0149.obstruction4786
  · exact NewCertificates0149.obstruction4787
  · exact NewCertificates0149.obstruction4788
  · exact NewCertificates0149.obstruction4789
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0149.obstruction4790
  · exact NewCertificates0149.obstruction4791
  · exact NewCertificates0149.obstruction4792
  · exact NewCertificates0149.obstruction4793
  · exact NewCertificates0149.obstruction4794
  · exact NewCertificates0149.obstruction4795
  · exact NewCertificates0149.obstruction4796
  · exact NewCertificates0149.obstruction4797
  · exact NewCertificates0149.obstruction4798
  · exact NewCertificates0149.obstruction4799
  · exact NewCertificates0150.obstruction4800
  · exact NewCertificates0150.obstruction4801
  · exact NewCertificates0150.obstruction4802
  · exact NewCertificates0150.obstruction4803
  · exact NewCertificates0150.obstruction4804
  · exact NewCertificates0150.obstruction4805
end Nut8.FiniteSupport102
