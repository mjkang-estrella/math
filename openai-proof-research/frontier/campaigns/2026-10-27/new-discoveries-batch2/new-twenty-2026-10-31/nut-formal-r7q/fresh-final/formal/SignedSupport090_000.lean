import SupportData090
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport090
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0129.C4150, NewCertificates0129.C4151, NewCertificates0129.C4152, NewCertificates0129.C4153, NewCertificates0129.C4154, NewCertificates0129.C4155, NewCertificates0129.C4156, NewCertificates0129.C4157, NewCertificates0129.C4158, NewCertificates0129.C4159, NewCertificates0130.C4160, NewCertificates0130.C4161, NewCertificates0130.C4162, NewCertificates0130.C4163, NewCertificates0130.C4164, NewCertificates0130.C4165} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0130.C4166, NewCertificates0130.C4167, NewCertificates0130.C4168, NewCertificates0130.C4169, NewCertificates0130.C4170, NewCertificates0130.C4171, NewCertificates0130.C4172, NewCertificates0130.C4173, NewCertificates0130.C4174, NewCertificates0130.C4175, NewCertificates0130.C4176, NewCertificates0130.C4177, NewCertificates0130.C4178, NewCertificates0130.C4179, NewCertificates0130.C4180, NewCertificates0130.C4181} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0130.C4182, NewCertificates0130.C4183, NewCertificates0130.C4184, NewCertificates0130.C4185, NewCertificates0130.C4186, NewCertificates0130.C4187, NewCertificates0130.C4188, NewCertificates0130.C4189, NewCertificates0130.C4190, NewCertificates0130.C4191, NewCertificates0131.C4192, NewCertificates0131.C4193, NewCertificates0131.C4194, NewCertificates0131.C4195, NewCertificates0131.C4196, NewCertificates0131.C4197} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0131.C4198, NewCertificates0131.C4199, NewCertificates0131.C4200, NewCertificates0131.C4201, NewCertificates0131.C4202, NewCertificates0131.C4203, NewCertificates0131.C4204, NewCertificates0131.C4205} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0129.obstruction4150
  · exact NewCertificates0129.obstruction4151
  · exact NewCertificates0129.obstruction4152
  · exact NewCertificates0129.obstruction4153
  · exact NewCertificates0129.obstruction4154
  · exact NewCertificates0129.obstruction4155
  · exact NewCertificates0129.obstruction4156
  · exact NewCertificates0129.obstruction4157
  · exact NewCertificates0129.obstruction4158
  · exact NewCertificates0129.obstruction4159
  · exact NewCertificates0130.obstruction4160
  · exact NewCertificates0130.obstruction4161
  · exact NewCertificates0130.obstruction4162
  · exact NewCertificates0130.obstruction4163
  · exact NewCertificates0130.obstruction4164
  · exact NewCertificates0130.obstruction4165
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0130.obstruction4166
  · exact NewCertificates0130.obstruction4167
  · exact NewCertificates0130.obstruction4168
  · exact NewCertificates0130.obstruction4169
  · exact NewCertificates0130.obstruction4170
  · exact NewCertificates0130.obstruction4171
  · exact NewCertificates0130.obstruction4172
  · exact NewCertificates0130.obstruction4173
  · exact NewCertificates0130.obstruction4174
  · exact NewCertificates0130.obstruction4175
  · exact NewCertificates0130.obstruction4176
  · exact NewCertificates0130.obstruction4177
  · exact NewCertificates0130.obstruction4178
  · exact NewCertificates0130.obstruction4179
  · exact NewCertificates0130.obstruction4180
  · exact NewCertificates0130.obstruction4181
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0130.obstruction4182
  · exact NewCertificates0130.obstruction4183
  · exact NewCertificates0130.obstruction4184
  · exact NewCertificates0130.obstruction4185
  · exact NewCertificates0130.obstruction4186
  · exact NewCertificates0130.obstruction4187
  · exact NewCertificates0130.obstruction4188
  · exact NewCertificates0130.obstruction4189
  · exact NewCertificates0130.obstruction4190
  · exact NewCertificates0130.obstruction4191
  · exact NewCertificates0131.obstruction4192
  · exact NewCertificates0131.obstruction4193
  · exact NewCertificates0131.obstruction4194
  · exact NewCertificates0131.obstruction4195
  · exact NewCertificates0131.obstruction4196
  · exact NewCertificates0131.obstruction4197
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0131.obstruction4198
  · exact NewCertificates0131.obstruction4199
  · exact NewCertificates0131.obstruction4200
  · exact NewCertificates0131.obstruction4201
  · exact NewCertificates0131.obstruction4202
  · exact NewCertificates0131.obstruction4203
  · exact NewCertificates0131.obstruction4204
  · exact NewCertificates0131.obstruction4205
end Nut8.FiniteSupport090
