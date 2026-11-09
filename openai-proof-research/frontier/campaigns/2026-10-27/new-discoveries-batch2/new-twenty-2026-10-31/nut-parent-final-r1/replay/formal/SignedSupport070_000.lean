import SupportData070
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport070
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0103.C3318, NewCertificates0103.C3319, NewCertificates0103.C3320, NewCertificates0103.C3321, NewCertificates0103.C3322, NewCertificates0103.C3323, NewCertificates0103.C3324, NewCertificates0103.C3325, NewCertificates0103.C3326, NewCertificates0103.C3327, NewCertificates0104.C3328, NewCertificates0104.C3329, NewCertificates0104.C3330, NewCertificates0104.C3331, NewCertificates0104.C3332, NewCertificates0104.C3333} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0104.C3334, NewCertificates0104.C3335, NewCertificates0104.C3336, NewCertificates0104.C3337, NewCertificates0104.C3338, NewCertificates0104.C3339, NewCertificates0104.C3340, NewCertificates0104.C3341} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0104.C3342, NewCertificates0104.C3343, NewCertificates0104.C3344, NewCertificates0104.C3345, NewCertificates0104.C3346, NewCertificates0104.C3347, NewCertificates0104.C3348, NewCertificates0104.C3349, NewCertificates0104.C3350, NewCertificates0104.C3351, NewCertificates0104.C3352, NewCertificates0104.C3353, NewCertificates0104.C3354, NewCertificates0104.C3355, NewCertificates0104.C3356, NewCertificates0104.C3357} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0104.C3358, NewCertificates0104.C3359, NewCertificates0105.C3360, NewCertificates0105.C3361, NewCertificates0105.C3362, NewCertificates0105.C3363, NewCertificates0105.C3364, NewCertificates0105.C3365} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0103.obstruction3318
  · exact NewCertificates0103.obstruction3319
  · exact NewCertificates0103.obstruction3320
  · exact NewCertificates0103.obstruction3321
  · exact NewCertificates0103.obstruction3322
  · exact NewCertificates0103.obstruction3323
  · exact NewCertificates0103.obstruction3324
  · exact NewCertificates0103.obstruction3325
  · exact NewCertificates0103.obstruction3326
  · exact NewCertificates0103.obstruction3327
  · exact NewCertificates0104.obstruction3328
  · exact NewCertificates0104.obstruction3329
  · exact NewCertificates0104.obstruction3330
  · exact NewCertificates0104.obstruction3331
  · exact NewCertificates0104.obstruction3332
  · exact NewCertificates0104.obstruction3333
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0104.obstruction3334
  · exact NewCertificates0104.obstruction3335
  · exact NewCertificates0104.obstruction3336
  · exact NewCertificates0104.obstruction3337
  · exact NewCertificates0104.obstruction3338
  · exact NewCertificates0104.obstruction3339
  · exact NewCertificates0104.obstruction3340
  · exact NewCertificates0104.obstruction3341
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0104.obstruction3342
  · exact NewCertificates0104.obstruction3343
  · exact NewCertificates0104.obstruction3344
  · exact NewCertificates0104.obstruction3345
  · exact NewCertificates0104.obstruction3346
  · exact NewCertificates0104.obstruction3347
  · exact NewCertificates0104.obstruction3348
  · exact NewCertificates0104.obstruction3349
  · exact NewCertificates0104.obstruction3350
  · exact NewCertificates0104.obstruction3351
  · exact NewCertificates0104.obstruction3352
  · exact NewCertificates0104.obstruction3353
  · exact NewCertificates0104.obstruction3354
  · exact NewCertificates0104.obstruction3355
  · exact NewCertificates0104.obstruction3356
  · exact NewCertificates0104.obstruction3357
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0104.obstruction3358
  · exact NewCertificates0104.obstruction3359
  · exact NewCertificates0105.obstruction3360
  · exact NewCertificates0105.obstruction3361
  · exact NewCertificates0105.obstruction3362
  · exact NewCertificates0105.obstruction3363
  · exact NewCertificates0105.obstruction3364
  · exact NewCertificates0105.obstruction3365
end Nut8.FiniteSupport070
