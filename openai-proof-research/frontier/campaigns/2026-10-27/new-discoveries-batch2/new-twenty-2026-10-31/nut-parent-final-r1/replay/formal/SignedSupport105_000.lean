import SupportData105
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport105
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0153.C4902, NewCertificates0153.C4903, NewCertificates0153.C4904, NewCertificates0153.C4905, NewCertificates0153.C4906, NewCertificates0153.C4907, NewCertificates0153.C4908, NewCertificates0153.C4909, NewCertificates0153.C4910, NewCertificates0153.C4911, NewCertificates0153.C4912, NewCertificates0153.C4913, NewCertificates0153.C4914, NewCertificates0153.C4915, NewCertificates0153.C4916, NewCertificates0153.C4917, NewCertificates0153.C4918, NewCertificates0153.C4919, NewCertificates0153.C4920, NewCertificates0153.C4921, NewCertificates0153.C4922, NewCertificates0153.C4923, NewCertificates0153.C4924, NewCertificates0153.C4925, NewCertificates0153.C4926, NewCertificates0153.C4927, NewCertificates0154.C4928, NewCertificates0154.C4929, NewCertificates0154.C4930, NewCertificates0154.C4931, NewCertificates0154.C4932, NewCertificates0154.C4933} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0154.C4934, NewCertificates0154.C4935, NewCertificates0154.C4936, NewCertificates0154.C4937, NewCertificates0154.C4938, NewCertificates0154.C4939, NewCertificates0154.C4940, NewCertificates0154.C4941, NewCertificates0154.C4942, NewCertificates0154.C4943, NewCertificates0154.C4944, NewCertificates0154.C4945, NewCertificates0154.C4946, NewCertificates0154.C4947, NewCertificates0154.C4948, NewCertificates0154.C4949} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0153.obstruction4902
  · exact NewCertificates0153.obstruction4903
  · exact NewCertificates0153.obstruction4904
  · exact NewCertificates0153.obstruction4905
  · exact NewCertificates0153.obstruction4906
  · exact NewCertificates0153.obstruction4907
  · exact NewCertificates0153.obstruction4908
  · exact NewCertificates0153.obstruction4909
  · exact NewCertificates0153.obstruction4910
  · exact NewCertificates0153.obstruction4911
  · exact NewCertificates0153.obstruction4912
  · exact NewCertificates0153.obstruction4913
  · exact NewCertificates0153.obstruction4914
  · exact NewCertificates0153.obstruction4915
  · exact NewCertificates0153.obstruction4916
  · exact NewCertificates0153.obstruction4917
  · exact NewCertificates0153.obstruction4918
  · exact NewCertificates0153.obstruction4919
  · exact NewCertificates0153.obstruction4920
  · exact NewCertificates0153.obstruction4921
  · exact NewCertificates0153.obstruction4922
  · exact NewCertificates0153.obstruction4923
  · exact NewCertificates0153.obstruction4924
  · exact NewCertificates0153.obstruction4925
  · exact NewCertificates0153.obstruction4926
  · exact NewCertificates0153.obstruction4927
  · exact NewCertificates0154.obstruction4928
  · exact NewCertificates0154.obstruction4929
  · exact NewCertificates0154.obstruction4930
  · exact NewCertificates0154.obstruction4931
  · exact NewCertificates0154.obstruction4932
  · exact NewCertificates0154.obstruction4933
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0154.obstruction4934
  · exact NewCertificates0154.obstruction4935
  · exact NewCertificates0154.obstruction4936
  · exact NewCertificates0154.obstruction4937
  · exact NewCertificates0154.obstruction4938
  · exact NewCertificates0154.obstruction4939
  · exact NewCertificates0154.obstruction4940
  · exact NewCertificates0154.obstruction4941
  · exact NewCertificates0154.obstruction4942
  · exact NewCertificates0154.obstruction4943
  · exact NewCertificates0154.obstruction4944
  · exact NewCertificates0154.obstruction4945
  · exact NewCertificates0154.obstruction4946
  · exact NewCertificates0154.obstruction4947
  · exact NewCertificates0154.obstruction4948
  · exact NewCertificates0154.obstruction4949
end Nut8.FiniteSupport105
