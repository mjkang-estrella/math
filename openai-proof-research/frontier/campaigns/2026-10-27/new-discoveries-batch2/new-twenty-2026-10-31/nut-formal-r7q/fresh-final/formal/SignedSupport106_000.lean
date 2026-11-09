import SupportData106
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport106
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0154.C4950, NewCertificates0154.C4951, NewCertificates0154.C4952, NewCertificates0154.C4953, NewCertificates0154.C4954, NewCertificates0154.C4955, NewCertificates0154.C4956, NewCertificates0154.C4957, NewCertificates0154.C4958, NewCertificates0154.C4959, NewCertificates0155.C4960, NewCertificates0155.C4961, NewCertificates0155.C4962, NewCertificates0155.C4963, NewCertificates0155.C4964, NewCertificates0155.C4965, NewCertificates0155.C4966, NewCertificates0155.C4967, NewCertificates0155.C4968, NewCertificates0155.C4969, NewCertificates0155.C4970, NewCertificates0155.C4971, NewCertificates0155.C4972, NewCertificates0155.C4973, NewCertificates0155.C4974, NewCertificates0155.C4975, NewCertificates0155.C4976, NewCertificates0155.C4977, NewCertificates0155.C4978, NewCertificates0155.C4979, NewCertificates0155.C4980, NewCertificates0155.C4981} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0155.C4982, NewCertificates0155.C4983, NewCertificates0155.C4984, NewCertificates0155.C4985, NewCertificates0155.C4986, NewCertificates0155.C4987, NewCertificates0155.C4988, NewCertificates0155.C4989, NewCertificates0155.C4990, NewCertificates0155.C4991, NewCertificates0156.C4992, NewCertificates0156.C4993, NewCertificates0156.C4994, NewCertificates0156.C4995, NewCertificates0156.C4996, NewCertificates0156.C4997} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0154.obstruction4950
  · exact NewCertificates0154.obstruction4951
  · exact NewCertificates0154.obstruction4952
  · exact NewCertificates0154.obstruction4953
  · exact NewCertificates0154.obstruction4954
  · exact NewCertificates0154.obstruction4955
  · exact NewCertificates0154.obstruction4956
  · exact NewCertificates0154.obstruction4957
  · exact NewCertificates0154.obstruction4958
  · exact NewCertificates0154.obstruction4959
  · exact NewCertificates0155.obstruction4960
  · exact NewCertificates0155.obstruction4961
  · exact NewCertificates0155.obstruction4962
  · exact NewCertificates0155.obstruction4963
  · exact NewCertificates0155.obstruction4964
  · exact NewCertificates0155.obstruction4965
  · exact NewCertificates0155.obstruction4966
  · exact NewCertificates0155.obstruction4967
  · exact NewCertificates0155.obstruction4968
  · exact NewCertificates0155.obstruction4969
  · exact NewCertificates0155.obstruction4970
  · exact NewCertificates0155.obstruction4971
  · exact NewCertificates0155.obstruction4972
  · exact NewCertificates0155.obstruction4973
  · exact NewCertificates0155.obstruction4974
  · exact NewCertificates0155.obstruction4975
  · exact NewCertificates0155.obstruction4976
  · exact NewCertificates0155.obstruction4977
  · exact NewCertificates0155.obstruction4978
  · exact NewCertificates0155.obstruction4979
  · exact NewCertificates0155.obstruction4980
  · exact NewCertificates0155.obstruction4981
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0155.obstruction4982
  · exact NewCertificates0155.obstruction4983
  · exact NewCertificates0155.obstruction4984
  · exact NewCertificates0155.obstruction4985
  · exact NewCertificates0155.obstruction4986
  · exact NewCertificates0155.obstruction4987
  · exact NewCertificates0155.obstruction4988
  · exact NewCertificates0155.obstruction4989
  · exact NewCertificates0155.obstruction4990
  · exact NewCertificates0155.obstruction4991
  · exact NewCertificates0156.obstruction4992
  · exact NewCertificates0156.obstruction4993
  · exact NewCertificates0156.obstruction4994
  · exact NewCertificates0156.obstruction4995
  · exact NewCertificates0156.obstruction4996
  · exact NewCertificates0156.obstruction4997
end Nut8.FiniteSupport106
