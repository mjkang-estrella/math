import SupportData003
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport003
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0004.C128, NewCertificates0004.C129, NewCertificates0004.C130, NewCertificates0004.C131, NewCertificates0004.C132, NewCertificates0004.C133, NewCertificates0004.C134, NewCertificates0004.C135, NewCertificates0004.C136, NewCertificates0004.C137, NewCertificates0004.C138, NewCertificates0004.C139, NewCertificates0004.C140, NewCertificates0004.C141, NewCertificates0004.C142, NewCertificates0004.C143, NewCertificates0004.C144, NewCertificates0004.C145, NewCertificates0004.C146, NewCertificates0004.C147, NewCertificates0004.C148, NewCertificates0004.C149, NewCertificates0004.C150, NewCertificates0004.C151, NewCertificates0004.C152, NewCertificates0004.C153, NewCertificates0004.C154, NewCertificates0004.C155, NewCertificates0004.C156, NewCertificates0004.C157, NewCertificates0004.C158, NewCertificates0004.C159} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0005.C160, NewCertificates0005.C161, NewCertificates0005.C162, NewCertificates0005.C163, NewCertificates0005.C164, NewCertificates0005.C165, NewCertificates0005.C166, NewCertificates0005.C167, NewCertificates0005.C168, NewCertificates0005.C169, NewCertificates0005.C170, NewCertificates0005.C171, NewCertificates0005.C172, NewCertificates0005.C173, NewCertificates0005.C174, NewCertificates0005.C175} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0005.C176, NewCertificates0005.C177, NewCertificates0005.C178, NewCertificates0005.C179, NewCertificates0005.C180, NewCertificates0005.C181, NewCertificates0005.C182, NewCertificates0005.C183, NewCertificates0005.C184, NewCertificates0005.C185, NewCertificates0005.C186, NewCertificates0005.C187, NewCertificates0005.C188, NewCertificates0005.C189, NewCertificates0005.C190, NewCertificates0005.C191} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0004.obstruction128
  · exact NewCertificates0004.obstruction129
  · exact NewCertificates0004.obstruction130
  · exact NewCertificates0004.obstruction131
  · exact NewCertificates0004.obstruction132
  · exact NewCertificates0004.obstruction133
  · exact NewCertificates0004.obstruction134
  · exact NewCertificates0004.obstruction135
  · exact NewCertificates0004.obstruction136
  · exact NewCertificates0004.obstruction137
  · exact NewCertificates0004.obstruction138
  · exact NewCertificates0004.obstruction139
  · exact NewCertificates0004.obstruction140
  · exact NewCertificates0004.obstruction141
  · exact NewCertificates0004.obstruction142
  · exact NewCertificates0004.obstruction143
  · exact NewCertificates0004.obstruction144
  · exact NewCertificates0004.obstruction145
  · exact NewCertificates0004.obstruction146
  · exact NewCertificates0004.obstruction147
  · exact NewCertificates0004.obstruction148
  · exact NewCertificates0004.obstruction149
  · exact NewCertificates0004.obstruction150
  · exact NewCertificates0004.obstruction151
  · exact NewCertificates0004.obstruction152
  · exact NewCertificates0004.obstruction153
  · exact NewCertificates0004.obstruction154
  · exact NewCertificates0004.obstruction155
  · exact NewCertificates0004.obstruction156
  · exact NewCertificates0004.obstruction157
  · exact NewCertificates0004.obstruction158
  · exact NewCertificates0004.obstruction159
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0005.obstruction160
  · exact NewCertificates0005.obstruction161
  · exact NewCertificates0005.obstruction162
  · exact NewCertificates0005.obstruction163
  · exact NewCertificates0005.obstruction164
  · exact NewCertificates0005.obstruction165
  · exact NewCertificates0005.obstruction166
  · exact NewCertificates0005.obstruction167
  · exact NewCertificates0005.obstruction168
  · exact NewCertificates0005.obstruction169
  · exact NewCertificates0005.obstruction170
  · exact NewCertificates0005.obstruction171
  · exact NewCertificates0005.obstruction172
  · exact NewCertificates0005.obstruction173
  · exact NewCertificates0005.obstruction174
  · exact NewCertificates0005.obstruction175
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0005.obstruction176
  · exact NewCertificates0005.obstruction177
  · exact NewCertificates0005.obstruction178
  · exact NewCertificates0005.obstruction179
  · exact NewCertificates0005.obstruction180
  · exact NewCertificates0005.obstruction181
  · exact NewCertificates0005.obstruction182
  · exact NewCertificates0005.obstruction183
  · exact NewCertificates0005.obstruction184
  · exact NewCertificates0005.obstruction185
  · exact NewCertificates0005.obstruction186
  · exact NewCertificates0005.obstruction187
  · exact NewCertificates0005.obstruction188
  · exact NewCertificates0005.obstruction189
  · exact NewCertificates0005.obstruction190
  · exact NewCertificates0005.obstruction191
end Nut8.FiniteSupport003
