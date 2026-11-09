import SupportData089
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport089
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0127.C4094, NewCertificates0127.C4095, NewCertificates0128.C4096, NewCertificates0128.C4097, NewCertificates0128.C4098, NewCertificates0128.C4099, NewCertificates0128.C4100, NewCertificates0128.C4101, NewCertificates0128.C4102, NewCertificates0128.C4103, NewCertificates0128.C4104, NewCertificates0128.C4105, NewCertificates0128.C4106, NewCertificates0128.C4107, NewCertificates0128.C4108, NewCertificates0128.C4109} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0128.C4110, NewCertificates0128.C4111, NewCertificates0128.C4112, NewCertificates0128.C4113, NewCertificates0128.C4114, NewCertificates0128.C4115, NewCertificates0128.C4116, NewCertificates0128.C4117, NewCertificates0128.C4118, NewCertificates0128.C4119, NewCertificates0128.C4120, NewCertificates0128.C4121, NewCertificates0128.C4122, NewCertificates0128.C4123, NewCertificates0128.C4124, NewCertificates0128.C4125} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0128.C4126, NewCertificates0128.C4127, NewCertificates0129.C4128, NewCertificates0129.C4129, NewCertificates0129.C4130, NewCertificates0129.C4131, NewCertificates0129.C4132, NewCertificates0129.C4133, NewCertificates0129.C4134, NewCertificates0129.C4135, NewCertificates0129.C4136, NewCertificates0129.C4137, NewCertificates0129.C4138, NewCertificates0129.C4139, NewCertificates0129.C4140, NewCertificates0129.C4141} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0129.C4142, NewCertificates0129.C4143, NewCertificates0129.C4144, NewCertificates0129.C4145, NewCertificates0129.C4146, NewCertificates0129.C4147, NewCertificates0129.C4148, NewCertificates0129.C4149} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0127.obstruction4094
  · exact NewCertificates0127.obstruction4095
  · exact NewCertificates0128.obstruction4096
  · exact NewCertificates0128.obstruction4097
  · exact NewCertificates0128.obstruction4098
  · exact NewCertificates0128.obstruction4099
  · exact NewCertificates0128.obstruction4100
  · exact NewCertificates0128.obstruction4101
  · exact NewCertificates0128.obstruction4102
  · exact NewCertificates0128.obstruction4103
  · exact NewCertificates0128.obstruction4104
  · exact NewCertificates0128.obstruction4105
  · exact NewCertificates0128.obstruction4106
  · exact NewCertificates0128.obstruction4107
  · exact NewCertificates0128.obstruction4108
  · exact NewCertificates0128.obstruction4109
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0128.obstruction4110
  · exact NewCertificates0128.obstruction4111
  · exact NewCertificates0128.obstruction4112
  · exact NewCertificates0128.obstruction4113
  · exact NewCertificates0128.obstruction4114
  · exact NewCertificates0128.obstruction4115
  · exact NewCertificates0128.obstruction4116
  · exact NewCertificates0128.obstruction4117
  · exact NewCertificates0128.obstruction4118
  · exact NewCertificates0128.obstruction4119
  · exact NewCertificates0128.obstruction4120
  · exact NewCertificates0128.obstruction4121
  · exact NewCertificates0128.obstruction4122
  · exact NewCertificates0128.obstruction4123
  · exact NewCertificates0128.obstruction4124
  · exact NewCertificates0128.obstruction4125
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0128.obstruction4126
  · exact NewCertificates0128.obstruction4127
  · exact NewCertificates0129.obstruction4128
  · exact NewCertificates0129.obstruction4129
  · exact NewCertificates0129.obstruction4130
  · exact NewCertificates0129.obstruction4131
  · exact NewCertificates0129.obstruction4132
  · exact NewCertificates0129.obstruction4133
  · exact NewCertificates0129.obstruction4134
  · exact NewCertificates0129.obstruction4135
  · exact NewCertificates0129.obstruction4136
  · exact NewCertificates0129.obstruction4137
  · exact NewCertificates0129.obstruction4138
  · exact NewCertificates0129.obstruction4139
  · exact NewCertificates0129.obstruction4140
  · exact NewCertificates0129.obstruction4141
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0129.obstruction4142
  · exact NewCertificates0129.obstruction4143
  · exact NewCertificates0129.obstruction4144
  · exact NewCertificates0129.obstruction4145
  · exact NewCertificates0129.obstruction4146
  · exact NewCertificates0129.obstruction4147
  · exact NewCertificates0129.obstruction4148
  · exact NewCertificates0129.obstruction4149
end Nut8.FiniteSupport089
