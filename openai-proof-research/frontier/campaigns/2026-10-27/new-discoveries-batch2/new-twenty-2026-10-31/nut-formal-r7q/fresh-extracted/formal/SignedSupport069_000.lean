import SupportData069
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport069
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0101.C3246, NewCertificates0101.C3247, NewCertificates0101.C3248, NewCertificates0101.C3249, NewCertificates0101.C3250, NewCertificates0101.C3251, NewCertificates0101.C3252, NewCertificates0101.C3253, NewCertificates0101.C3254, NewCertificates0101.C3255, NewCertificates0101.C3256, NewCertificates0101.C3257, NewCertificates0101.C3258, NewCertificates0101.C3259, NewCertificates0101.C3260, NewCertificates0101.C3261} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0101.C3262, NewCertificates0101.C3263, NewCertificates0102.C3264, NewCertificates0102.C3265, NewCertificates0102.C3266, NewCertificates0102.C3267, NewCertificates0102.C3268, NewCertificates0102.C3269} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0102.C3270, NewCertificates0102.C3271, NewCertificates0102.C3272, NewCertificates0102.C3273, NewCertificates0102.C3274, NewCertificates0102.C3275, NewCertificates0102.C3276, NewCertificates0102.C3277, NewCertificates0102.C3278, NewCertificates0102.C3279, NewCertificates0102.C3280, NewCertificates0102.C3281, NewCertificates0102.C3282, NewCertificates0102.C3283, NewCertificates0102.C3284, NewCertificates0102.C3285} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0102.C3286, NewCertificates0102.C3287, NewCertificates0102.C3288, NewCertificates0102.C3289, NewCertificates0102.C3290, NewCertificates0102.C3291, NewCertificates0102.C3292, NewCertificates0102.C3293, NewCertificates0102.C3294, NewCertificates0102.C3295, NewCertificates0103.C3296, NewCertificates0103.C3297, NewCertificates0103.C3298, NewCertificates0103.C3299, NewCertificates0103.C3300, NewCertificates0103.C3301} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0101.obstruction3246
  · exact NewCertificates0101.obstruction3247
  · exact NewCertificates0101.obstruction3248
  · exact NewCertificates0101.obstruction3249
  · exact NewCertificates0101.obstruction3250
  · exact NewCertificates0101.obstruction3251
  · exact NewCertificates0101.obstruction3252
  · exact NewCertificates0101.obstruction3253
  · exact NewCertificates0101.obstruction3254
  · exact NewCertificates0101.obstruction3255
  · exact NewCertificates0101.obstruction3256
  · exact NewCertificates0101.obstruction3257
  · exact NewCertificates0101.obstruction3258
  · exact NewCertificates0101.obstruction3259
  · exact NewCertificates0101.obstruction3260
  · exact NewCertificates0101.obstruction3261
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0101.obstruction3262
  · exact NewCertificates0101.obstruction3263
  · exact NewCertificates0102.obstruction3264
  · exact NewCertificates0102.obstruction3265
  · exact NewCertificates0102.obstruction3266
  · exact NewCertificates0102.obstruction3267
  · exact NewCertificates0102.obstruction3268
  · exact NewCertificates0102.obstruction3269
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0102.obstruction3270
  · exact NewCertificates0102.obstruction3271
  · exact NewCertificates0102.obstruction3272
  · exact NewCertificates0102.obstruction3273
  · exact NewCertificates0102.obstruction3274
  · exact NewCertificates0102.obstruction3275
  · exact NewCertificates0102.obstruction3276
  · exact NewCertificates0102.obstruction3277
  · exact NewCertificates0102.obstruction3278
  · exact NewCertificates0102.obstruction3279
  · exact NewCertificates0102.obstruction3280
  · exact NewCertificates0102.obstruction3281
  · exact NewCertificates0102.obstruction3282
  · exact NewCertificates0102.obstruction3283
  · exact NewCertificates0102.obstruction3284
  · exact NewCertificates0102.obstruction3285
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0102.obstruction3286
  · exact NewCertificates0102.obstruction3287
  · exact NewCertificates0102.obstruction3288
  · exact NewCertificates0102.obstruction3289
  · exact NewCertificates0102.obstruction3290
  · exact NewCertificates0102.obstruction3291
  · exact NewCertificates0102.obstruction3292
  · exact NewCertificates0102.obstruction3293
  · exact NewCertificates0102.obstruction3294
  · exact NewCertificates0102.obstruction3295
  · exact NewCertificates0103.obstruction3296
  · exact NewCertificates0103.obstruction3297
  · exact NewCertificates0103.obstruction3298
  · exact NewCertificates0103.obstruction3299
  · exact NewCertificates0103.obstruction3300
  · exact NewCertificates0103.obstruction3301
end Nut8.FiniteSupport069
