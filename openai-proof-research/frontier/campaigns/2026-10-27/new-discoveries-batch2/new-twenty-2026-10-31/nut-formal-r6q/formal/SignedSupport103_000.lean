import SupportData103
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport103
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0150.C4806, NewCertificates0150.C4807, NewCertificates0150.C4808, NewCertificates0150.C4809, NewCertificates0150.C4810, NewCertificates0150.C4811, NewCertificates0150.C4812, NewCertificates0150.C4813, NewCertificates0150.C4814, NewCertificates0150.C4815, NewCertificates0150.C4816, NewCertificates0150.C4817, NewCertificates0150.C4818, NewCertificates0150.C4819, NewCertificates0150.C4820, NewCertificates0150.C4821, NewCertificates0150.C4822, NewCertificates0150.C4823, NewCertificates0150.C4824, NewCertificates0150.C4825, NewCertificates0150.C4826, NewCertificates0150.C4827, NewCertificates0150.C4828, NewCertificates0150.C4829, NewCertificates0150.C4830, NewCertificates0150.C4831, NewCertificates0151.C4832, NewCertificates0151.C4833, NewCertificates0151.C4834, NewCertificates0151.C4835, NewCertificates0151.C4836, NewCertificates0151.C4837} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0151.C4838, NewCertificates0151.C4839, NewCertificates0151.C4840, NewCertificates0151.C4841, NewCertificates0151.C4842, NewCertificates0151.C4843, NewCertificates0151.C4844, NewCertificates0151.C4845, NewCertificates0151.C4846, NewCertificates0151.C4847, NewCertificates0151.C4848, NewCertificates0151.C4849, NewCertificates0151.C4850, NewCertificates0151.C4851, NewCertificates0151.C4852, NewCertificates0151.C4853} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0150.obstruction4806
  · exact NewCertificates0150.obstruction4807
  · exact NewCertificates0150.obstruction4808
  · exact NewCertificates0150.obstruction4809
  · exact NewCertificates0150.obstruction4810
  · exact NewCertificates0150.obstruction4811
  · exact NewCertificates0150.obstruction4812
  · exact NewCertificates0150.obstruction4813
  · exact NewCertificates0150.obstruction4814
  · exact NewCertificates0150.obstruction4815
  · exact NewCertificates0150.obstruction4816
  · exact NewCertificates0150.obstruction4817
  · exact NewCertificates0150.obstruction4818
  · exact NewCertificates0150.obstruction4819
  · exact NewCertificates0150.obstruction4820
  · exact NewCertificates0150.obstruction4821
  · exact NewCertificates0150.obstruction4822
  · exact NewCertificates0150.obstruction4823
  · exact NewCertificates0150.obstruction4824
  · exact NewCertificates0150.obstruction4825
  · exact NewCertificates0150.obstruction4826
  · exact NewCertificates0150.obstruction4827
  · exact NewCertificates0150.obstruction4828
  · exact NewCertificates0150.obstruction4829
  · exact NewCertificates0150.obstruction4830
  · exact NewCertificates0150.obstruction4831
  · exact NewCertificates0151.obstruction4832
  · exact NewCertificates0151.obstruction4833
  · exact NewCertificates0151.obstruction4834
  · exact NewCertificates0151.obstruction4835
  · exact NewCertificates0151.obstruction4836
  · exact NewCertificates0151.obstruction4837
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0151.obstruction4838
  · exact NewCertificates0151.obstruction4839
  · exact NewCertificates0151.obstruction4840
  · exact NewCertificates0151.obstruction4841
  · exact NewCertificates0151.obstruction4842
  · exact NewCertificates0151.obstruction4843
  · exact NewCertificates0151.obstruction4844
  · exact NewCertificates0151.obstruction4845
  · exact NewCertificates0151.obstruction4846
  · exact NewCertificates0151.obstruction4847
  · exact NewCertificates0151.obstruction4848
  · exact NewCertificates0151.obstruction4849
  · exact NewCertificates0151.obstruction4850
  · exact NewCertificates0151.obstruction4851
  · exact NewCertificates0151.obstruction4852
  · exact NewCertificates0151.obstruction4853
end Nut8.FiniteSupport103
