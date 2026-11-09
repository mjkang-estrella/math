import SupportData088
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport088
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0126.C4062, NewCertificates0126.C4063, NewCertificates0127.C4064, NewCertificates0127.C4065, NewCertificates0127.C4066, NewCertificates0127.C4067, NewCertificates0127.C4068, NewCertificates0127.C4069, NewCertificates0127.C4070, NewCertificates0127.C4071, NewCertificates0127.C4072, NewCertificates0127.C4073, NewCertificates0127.C4074, NewCertificates0127.C4075, NewCertificates0127.C4076, NewCertificates0127.C4077, NewCertificates0127.C4078, NewCertificates0127.C4079, NewCertificates0127.C4080, NewCertificates0127.C4081, NewCertificates0127.C4082, NewCertificates0127.C4083, NewCertificates0127.C4084, NewCertificates0127.C4085, NewCertificates0127.C4086, NewCertificates0127.C4087, NewCertificates0127.C4088, NewCertificates0127.C4089, NewCertificates0127.C4090, NewCertificates0127.C4091, NewCertificates0127.C4092, NewCertificates0127.C4093} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0126.obstruction4062
  · exact NewCertificates0126.obstruction4063
  · exact NewCertificates0127.obstruction4064
  · exact NewCertificates0127.obstruction4065
  · exact NewCertificates0127.obstruction4066
  · exact NewCertificates0127.obstruction4067
  · exact NewCertificates0127.obstruction4068
  · exact NewCertificates0127.obstruction4069
  · exact NewCertificates0127.obstruction4070
  · exact NewCertificates0127.obstruction4071
  · exact NewCertificates0127.obstruction4072
  · exact NewCertificates0127.obstruction4073
  · exact NewCertificates0127.obstruction4074
  · exact NewCertificates0127.obstruction4075
  · exact NewCertificates0127.obstruction4076
  · exact NewCertificates0127.obstruction4077
  · exact NewCertificates0127.obstruction4078
  · exact NewCertificates0127.obstruction4079
  · exact NewCertificates0127.obstruction4080
  · exact NewCertificates0127.obstruction4081
  · exact NewCertificates0127.obstruction4082
  · exact NewCertificates0127.obstruction4083
  · exact NewCertificates0127.obstruction4084
  · exact NewCertificates0127.obstruction4085
  · exact NewCertificates0127.obstruction4086
  · exact NewCertificates0127.obstruction4087
  · exact NewCertificates0127.obstruction4088
  · exact NewCertificates0127.obstruction4089
  · exact NewCertificates0127.obstruction4090
  · exact NewCertificates0127.obstruction4091
  · exact NewCertificates0127.obstruction4092
  · exact NewCertificates0127.obstruction4093
end Nut8.FiniteSupport088
