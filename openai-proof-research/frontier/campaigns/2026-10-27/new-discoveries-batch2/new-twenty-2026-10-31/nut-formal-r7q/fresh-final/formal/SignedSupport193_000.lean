import SupportData193
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport193
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0285.C9124, NewCertificates0285.C9125, NewCertificates0285.C9126, NewCertificates0285.C9127, NewCertificates0285.C9128, NewCertificates0285.C9129, NewCertificates0285.C9130, NewCertificates0285.C9131, NewCertificates0285.C9132, NewCertificates0285.C9133, NewCertificates0285.C9134, NewCertificates0285.C9135, NewCertificates0285.C9136, NewCertificates0285.C9137, NewCertificates0285.C9138, NewCertificates0285.C9139, NewCertificates0285.C9140, NewCertificates0285.C9141, NewCertificates0285.C9142, NewCertificates0285.C9143, NewCertificates0285.C9144, NewCertificates0285.C9145, NewCertificates0285.C9146, NewCertificates0285.C9147, NewCertificates0285.C9148, NewCertificates0285.C9149, NewCertificates0285.C9150, NewCertificates0285.C9151, NewCertificates0286.C9152, NewCertificates0286.C9153, NewCertificates0286.C9154, NewCertificates0286.C9155} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0286.C9156, NewCertificates0286.C9157, NewCertificates0286.C9158, NewCertificates0286.C9159, NewCertificates0286.C9160, NewCertificates0286.C9161, NewCertificates0286.C9162, NewCertificates0286.C9163, NewCertificates0286.C9164, NewCertificates0286.C9165, NewCertificates0286.C9166, NewCertificates0286.C9167, NewCertificates0286.C9168, NewCertificates0286.C9169, NewCertificates0286.C9170, NewCertificates0286.C9171} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0285.obstruction9124
  · exact NewCertificates0285.obstruction9125
  · exact NewCertificates0285.obstruction9126
  · exact NewCertificates0285.obstruction9127
  · exact NewCertificates0285.obstruction9128
  · exact NewCertificates0285.obstruction9129
  · exact NewCertificates0285.obstruction9130
  · exact NewCertificates0285.obstruction9131
  · exact NewCertificates0285.obstruction9132
  · exact NewCertificates0285.obstruction9133
  · exact NewCertificates0285.obstruction9134
  · exact NewCertificates0285.obstruction9135
  · exact NewCertificates0285.obstruction9136
  · exact NewCertificates0285.obstruction9137
  · exact NewCertificates0285.obstruction9138
  · exact NewCertificates0285.obstruction9139
  · exact NewCertificates0285.obstruction9140
  · exact NewCertificates0285.obstruction9141
  · exact NewCertificates0285.obstruction9142
  · exact NewCertificates0285.obstruction9143
  · exact NewCertificates0285.obstruction9144
  · exact NewCertificates0285.obstruction9145
  · exact NewCertificates0285.obstruction9146
  · exact NewCertificates0285.obstruction9147
  · exact NewCertificates0285.obstruction9148
  · exact NewCertificates0285.obstruction9149
  · exact NewCertificates0285.obstruction9150
  · exact NewCertificates0285.obstruction9151
  · exact NewCertificates0286.obstruction9152
  · exact NewCertificates0286.obstruction9153
  · exact NewCertificates0286.obstruction9154
  · exact NewCertificates0286.obstruction9155
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0286.obstruction9156
  · exact NewCertificates0286.obstruction9157
  · exact NewCertificates0286.obstruction9158
  · exact NewCertificates0286.obstruction9159
  · exact NewCertificates0286.obstruction9160
  · exact NewCertificates0286.obstruction9161
  · exact NewCertificates0286.obstruction9162
  · exact NewCertificates0286.obstruction9163
  · exact NewCertificates0286.obstruction9164
  · exact NewCertificates0286.obstruction9165
  · exact NewCertificates0286.obstruction9166
  · exact NewCertificates0286.obstruction9167
  · exact NewCertificates0286.obstruction9168
  · exact NewCertificates0286.obstruction9169
  · exact NewCertificates0286.obstruction9170
  · exact NewCertificates0286.obstruction9171
end Nut8.FiniteSupport193
