import SupportData104
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport104
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0151.C4854, NewCertificates0151.C4855, NewCertificates0151.C4856, NewCertificates0151.C4857, NewCertificates0151.C4858, NewCertificates0151.C4859, NewCertificates0151.C4860, NewCertificates0151.C4861, NewCertificates0151.C4862, NewCertificates0151.C4863, NewCertificates0152.C4864, NewCertificates0152.C4865, NewCertificates0152.C4866, NewCertificates0152.C4867, NewCertificates0152.C4868, NewCertificates0152.C4869, NewCertificates0152.C4870, NewCertificates0152.C4871, NewCertificates0152.C4872, NewCertificates0152.C4873, NewCertificates0152.C4874, NewCertificates0152.C4875, NewCertificates0152.C4876, NewCertificates0152.C4877, NewCertificates0152.C4878, NewCertificates0152.C4879, NewCertificates0152.C4880, NewCertificates0152.C4881, NewCertificates0152.C4882, NewCertificates0152.C4883, NewCertificates0152.C4884, NewCertificates0152.C4885} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0152.C4886, NewCertificates0152.C4887, NewCertificates0152.C4888, NewCertificates0152.C4889, NewCertificates0152.C4890, NewCertificates0152.C4891, NewCertificates0152.C4892, NewCertificates0152.C4893, NewCertificates0152.C4894, NewCertificates0152.C4895, NewCertificates0153.C4896, NewCertificates0153.C4897, NewCertificates0153.C4898, NewCertificates0153.C4899, NewCertificates0153.C4900, NewCertificates0153.C4901} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0151.obstruction4854
  · exact NewCertificates0151.obstruction4855
  · exact NewCertificates0151.obstruction4856
  · exact NewCertificates0151.obstruction4857
  · exact NewCertificates0151.obstruction4858
  · exact NewCertificates0151.obstruction4859
  · exact NewCertificates0151.obstruction4860
  · exact NewCertificates0151.obstruction4861
  · exact NewCertificates0151.obstruction4862
  · exact NewCertificates0151.obstruction4863
  · exact NewCertificates0152.obstruction4864
  · exact NewCertificates0152.obstruction4865
  · exact NewCertificates0152.obstruction4866
  · exact NewCertificates0152.obstruction4867
  · exact NewCertificates0152.obstruction4868
  · exact NewCertificates0152.obstruction4869
  · exact NewCertificates0152.obstruction4870
  · exact NewCertificates0152.obstruction4871
  · exact NewCertificates0152.obstruction4872
  · exact NewCertificates0152.obstruction4873
  · exact NewCertificates0152.obstruction4874
  · exact NewCertificates0152.obstruction4875
  · exact NewCertificates0152.obstruction4876
  · exact NewCertificates0152.obstruction4877
  · exact NewCertificates0152.obstruction4878
  · exact NewCertificates0152.obstruction4879
  · exact NewCertificates0152.obstruction4880
  · exact NewCertificates0152.obstruction4881
  · exact NewCertificates0152.obstruction4882
  · exact NewCertificates0152.obstruction4883
  · exact NewCertificates0152.obstruction4884
  · exact NewCertificates0152.obstruction4885
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0152.obstruction4886
  · exact NewCertificates0152.obstruction4887
  · exact NewCertificates0152.obstruction4888
  · exact NewCertificates0152.obstruction4889
  · exact NewCertificates0152.obstruction4890
  · exact NewCertificates0152.obstruction4891
  · exact NewCertificates0152.obstruction4892
  · exact NewCertificates0152.obstruction4893
  · exact NewCertificates0152.obstruction4894
  · exact NewCertificates0152.obstruction4895
  · exact NewCertificates0153.obstruction4896
  · exact NewCertificates0153.obstruction4897
  · exact NewCertificates0153.obstruction4898
  · exact NewCertificates0153.obstruction4899
  · exact NewCertificates0153.obstruction4900
  · exact NewCertificates0153.obstruction4901
end Nut8.FiniteSupport104
