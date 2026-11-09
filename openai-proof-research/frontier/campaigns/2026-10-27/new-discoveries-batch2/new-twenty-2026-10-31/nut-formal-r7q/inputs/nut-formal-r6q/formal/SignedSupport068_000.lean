import SupportData068
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport068
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0099.C3174, NewCertificates0099.C3175, NewCertificates0099.C3176, NewCertificates0099.C3177, NewCertificates0099.C3178, NewCertificates0099.C3179, NewCertificates0099.C3180, NewCertificates0099.C3181, NewCertificates0099.C3182, NewCertificates0099.C3183, NewCertificates0099.C3184, NewCertificates0099.C3185, NewCertificates0099.C3186, NewCertificates0099.C3187, NewCertificates0099.C3188, NewCertificates0099.C3189} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0099.C3190, NewCertificates0099.C3191, NewCertificates0099.C3192, NewCertificates0099.C3193, NewCertificates0099.C3194, NewCertificates0099.C3195, NewCertificates0099.C3196, NewCertificates0099.C3197, NewCertificates0099.C3198, NewCertificates0099.C3199, NewCertificates0100.C3200, NewCertificates0100.C3201, NewCertificates0100.C3202, NewCertificates0100.C3203, NewCertificates0100.C3204, NewCertificates0100.C3205} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0100.C3206, NewCertificates0100.C3207, NewCertificates0100.C3208, NewCertificates0100.C3209, NewCertificates0100.C3210, NewCertificates0100.C3211, NewCertificates0100.C3212, NewCertificates0100.C3213} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0100.C3214, NewCertificates0100.C3215, NewCertificates0100.C3216, NewCertificates0100.C3217, NewCertificates0100.C3218, NewCertificates0100.C3219, NewCertificates0100.C3220, NewCertificates0100.C3221} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0099.obstruction3174
  · exact NewCertificates0099.obstruction3175
  · exact NewCertificates0099.obstruction3176
  · exact NewCertificates0099.obstruction3177
  · exact NewCertificates0099.obstruction3178
  · exact NewCertificates0099.obstruction3179
  · exact NewCertificates0099.obstruction3180
  · exact NewCertificates0099.obstruction3181
  · exact NewCertificates0099.obstruction3182
  · exact NewCertificates0099.obstruction3183
  · exact NewCertificates0099.obstruction3184
  · exact NewCertificates0099.obstruction3185
  · exact NewCertificates0099.obstruction3186
  · exact NewCertificates0099.obstruction3187
  · exact NewCertificates0099.obstruction3188
  · exact NewCertificates0099.obstruction3189
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0099.obstruction3190
  · exact NewCertificates0099.obstruction3191
  · exact NewCertificates0099.obstruction3192
  · exact NewCertificates0099.obstruction3193
  · exact NewCertificates0099.obstruction3194
  · exact NewCertificates0099.obstruction3195
  · exact NewCertificates0099.obstruction3196
  · exact NewCertificates0099.obstruction3197
  · exact NewCertificates0099.obstruction3198
  · exact NewCertificates0099.obstruction3199
  · exact NewCertificates0100.obstruction3200
  · exact NewCertificates0100.obstruction3201
  · exact NewCertificates0100.obstruction3202
  · exact NewCertificates0100.obstruction3203
  · exact NewCertificates0100.obstruction3204
  · exact NewCertificates0100.obstruction3205
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0100.obstruction3206
  · exact NewCertificates0100.obstruction3207
  · exact NewCertificates0100.obstruction3208
  · exact NewCertificates0100.obstruction3209
  · exact NewCertificates0100.obstruction3210
  · exact NewCertificates0100.obstruction3211
  · exact NewCertificates0100.obstruction3212
  · exact NewCertificates0100.obstruction3213
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0100.obstruction3214
  · exact NewCertificates0100.obstruction3215
  · exact NewCertificates0100.obstruction3216
  · exact NewCertificates0100.obstruction3217
  · exact NewCertificates0100.obstruction3218
  · exact NewCertificates0100.obstruction3219
  · exact NewCertificates0100.obstruction3220
  · exact NewCertificates0100.obstruction3221
end Nut8.FiniteSupport068
