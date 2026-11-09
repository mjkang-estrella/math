import SupportData176
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport176
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0255.C8164, NewCertificates0255.C8165, NewCertificates0255.C8166, NewCertificates0255.C8167, NewCertificates0255.C8168, NewCertificates0255.C8169, NewCertificates0255.C8170, NewCertificates0255.C8171, NewCertificates0255.C8172, NewCertificates0255.C8173, NewCertificates0255.C8174, NewCertificates0255.C8175, NewCertificates0255.C8176, NewCertificates0255.C8177, NewCertificates0255.C8178, NewCertificates0255.C8179} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0255.C8180, NewCertificates0255.C8181, NewCertificates0255.C8182, NewCertificates0255.C8183, NewCertificates0255.C8184, NewCertificates0255.C8185, NewCertificates0255.C8186, NewCertificates0255.C8187, NewCertificates0255.C8188, NewCertificates0255.C8189, NewCertificates0255.C8190, NewCertificates0255.C8191, NewCertificates0256.C8192, NewCertificates0256.C8193, NewCertificates0256.C8194, NewCertificates0256.C8195} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0256.C8196, NewCertificates0256.C8197, NewCertificates0256.C8198, NewCertificates0256.C8199, NewCertificates0256.C8200, NewCertificates0256.C8201, NewCertificates0256.C8202, NewCertificates0256.C8203, NewCertificates0256.C8204, NewCertificates0256.C8205, NewCertificates0256.C8206, NewCertificates0256.C8207, NewCertificates0256.C8208, NewCertificates0256.C8209, NewCertificates0256.C8210, NewCertificates0256.C8211} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0256.C8212, NewCertificates0256.C8213, NewCertificates0256.C8214, NewCertificates0256.C8215, NewCertificates0256.C8216, NewCertificates0256.C8217, NewCertificates0256.C8218, NewCertificates0256.C8219} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0255.obstruction8164
  · exact NewCertificates0255.obstruction8165
  · exact NewCertificates0255.obstruction8166
  · exact NewCertificates0255.obstruction8167
  · exact NewCertificates0255.obstruction8168
  · exact NewCertificates0255.obstruction8169
  · exact NewCertificates0255.obstruction8170
  · exact NewCertificates0255.obstruction8171
  · exact NewCertificates0255.obstruction8172
  · exact NewCertificates0255.obstruction8173
  · exact NewCertificates0255.obstruction8174
  · exact NewCertificates0255.obstruction8175
  · exact NewCertificates0255.obstruction8176
  · exact NewCertificates0255.obstruction8177
  · exact NewCertificates0255.obstruction8178
  · exact NewCertificates0255.obstruction8179
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0255.obstruction8180
  · exact NewCertificates0255.obstruction8181
  · exact NewCertificates0255.obstruction8182
  · exact NewCertificates0255.obstruction8183
  · exact NewCertificates0255.obstruction8184
  · exact NewCertificates0255.obstruction8185
  · exact NewCertificates0255.obstruction8186
  · exact NewCertificates0255.obstruction8187
  · exact NewCertificates0255.obstruction8188
  · exact NewCertificates0255.obstruction8189
  · exact NewCertificates0255.obstruction8190
  · exact NewCertificates0255.obstruction8191
  · exact NewCertificates0256.obstruction8192
  · exact NewCertificates0256.obstruction8193
  · exact NewCertificates0256.obstruction8194
  · exact NewCertificates0256.obstruction8195
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0256.obstruction8196
  · exact NewCertificates0256.obstruction8197
  · exact NewCertificates0256.obstruction8198
  · exact NewCertificates0256.obstruction8199
  · exact NewCertificates0256.obstruction8200
  · exact NewCertificates0256.obstruction8201
  · exact NewCertificates0256.obstruction8202
  · exact NewCertificates0256.obstruction8203
  · exact NewCertificates0256.obstruction8204
  · exact NewCertificates0256.obstruction8205
  · exact NewCertificates0256.obstruction8206
  · exact NewCertificates0256.obstruction8207
  · exact NewCertificates0256.obstruction8208
  · exact NewCertificates0256.obstruction8209
  · exact NewCertificates0256.obstruction8210
  · exact NewCertificates0256.obstruction8211
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0256.obstruction8212
  · exact NewCertificates0256.obstruction8213
  · exact NewCertificates0256.obstruction8214
  · exact NewCertificates0256.obstruction8215
  · exact NewCertificates0256.obstruction8216
  · exact NewCertificates0256.obstruction8217
  · exact NewCertificates0256.obstruction8218
  · exact NewCertificates0256.obstruction8219
end Nut8.FiniteSupport176
