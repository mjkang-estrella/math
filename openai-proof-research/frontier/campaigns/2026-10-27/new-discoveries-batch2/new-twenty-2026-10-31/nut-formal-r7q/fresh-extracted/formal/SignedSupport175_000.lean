import SupportData175
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport175
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0253.C8116, NewCertificates0253.C8117, NewCertificates0253.C8118, NewCertificates0253.C8119, NewCertificates0253.C8120, NewCertificates0253.C8121, NewCertificates0253.C8122, NewCertificates0253.C8123, NewCertificates0253.C8124, NewCertificates0253.C8125, NewCertificates0253.C8126, NewCertificates0253.C8127, NewCertificates0254.C8128, NewCertificates0254.C8129, NewCertificates0254.C8130, NewCertificates0254.C8131} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0254.C8132, NewCertificates0254.C8133, NewCertificates0254.C8134, NewCertificates0254.C8135, NewCertificates0254.C8136, NewCertificates0254.C8137, NewCertificates0254.C8138, NewCertificates0254.C8139, NewCertificates0254.C8140, NewCertificates0254.C8141, NewCertificates0254.C8142, NewCertificates0254.C8143, NewCertificates0254.C8144, NewCertificates0254.C8145, NewCertificates0254.C8146, NewCertificates0254.C8147} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0254.C8148, NewCertificates0254.C8149, NewCertificates0254.C8150, NewCertificates0254.C8151, NewCertificates0254.C8152, NewCertificates0254.C8153, NewCertificates0254.C8154, NewCertificates0254.C8155} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0254.C8156, NewCertificates0254.C8157, NewCertificates0254.C8158, NewCertificates0254.C8159, NewCertificates0255.C8160, NewCertificates0255.C8161, NewCertificates0255.C8162, NewCertificates0255.C8163} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0253.obstruction8116
  · exact NewCertificates0253.obstruction8117
  · exact NewCertificates0253.obstruction8118
  · exact NewCertificates0253.obstruction8119
  · exact NewCertificates0253.obstruction8120
  · exact NewCertificates0253.obstruction8121
  · exact NewCertificates0253.obstruction8122
  · exact NewCertificates0253.obstruction8123
  · exact NewCertificates0253.obstruction8124
  · exact NewCertificates0253.obstruction8125
  · exact NewCertificates0253.obstruction8126
  · exact NewCertificates0253.obstruction8127
  · exact NewCertificates0254.obstruction8128
  · exact NewCertificates0254.obstruction8129
  · exact NewCertificates0254.obstruction8130
  · exact NewCertificates0254.obstruction8131
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0254.obstruction8132
  · exact NewCertificates0254.obstruction8133
  · exact NewCertificates0254.obstruction8134
  · exact NewCertificates0254.obstruction8135
  · exact NewCertificates0254.obstruction8136
  · exact NewCertificates0254.obstruction8137
  · exact NewCertificates0254.obstruction8138
  · exact NewCertificates0254.obstruction8139
  · exact NewCertificates0254.obstruction8140
  · exact NewCertificates0254.obstruction8141
  · exact NewCertificates0254.obstruction8142
  · exact NewCertificates0254.obstruction8143
  · exact NewCertificates0254.obstruction8144
  · exact NewCertificates0254.obstruction8145
  · exact NewCertificates0254.obstruction8146
  · exact NewCertificates0254.obstruction8147
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0254.obstruction8148
  · exact NewCertificates0254.obstruction8149
  · exact NewCertificates0254.obstruction8150
  · exact NewCertificates0254.obstruction8151
  · exact NewCertificates0254.obstruction8152
  · exact NewCertificates0254.obstruction8153
  · exact NewCertificates0254.obstruction8154
  · exact NewCertificates0254.obstruction8155
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0254.obstruction8156
  · exact NewCertificates0254.obstruction8157
  · exact NewCertificates0254.obstruction8158
  · exact NewCertificates0254.obstruction8159
  · exact NewCertificates0255.obstruction8160
  · exact NewCertificates0255.obstruction8161
  · exact NewCertificates0255.obstruction8162
  · exact NewCertificates0255.obstruction8163
end Nut8.FiniteSupport175
