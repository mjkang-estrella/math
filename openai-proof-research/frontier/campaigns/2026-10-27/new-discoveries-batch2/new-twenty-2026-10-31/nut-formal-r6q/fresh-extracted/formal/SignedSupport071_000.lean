import SupportData071
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport071
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0105.C3390, NewCertificates0105.C3391, NewCertificates0106.C3392, NewCertificates0106.C3393, NewCertificates0106.C3394, NewCertificates0106.C3395, NewCertificates0106.C3396, NewCertificates0106.C3397, NewCertificates0106.C3398, NewCertificates0106.C3399, NewCertificates0106.C3400, NewCertificates0106.C3401, NewCertificates0106.C3402, NewCertificates0106.C3403, NewCertificates0106.C3404, NewCertificates0106.C3405} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0106.C3406, NewCertificates0106.C3407, NewCertificates0106.C3408, NewCertificates0106.C3409, NewCertificates0106.C3410, NewCertificates0106.C3411, NewCertificates0106.C3412, NewCertificates0106.C3413, NewCertificates0106.C3414, NewCertificates0106.C3415, NewCertificates0106.C3416, NewCertificates0106.C3417, NewCertificates0106.C3418, NewCertificates0106.C3419, NewCertificates0106.C3420, NewCertificates0106.C3421} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0106.C3422, NewCertificates0106.C3423, NewCertificates0107.C3424, NewCertificates0107.C3425, NewCertificates0107.C3426, NewCertificates0107.C3427, NewCertificates0107.C3428, NewCertificates0107.C3429, NewCertificates0107.C3430, NewCertificates0107.C3431, NewCertificates0107.C3432, NewCertificates0107.C3433, NewCertificates0107.C3434, NewCertificates0107.C3435, NewCertificates0107.C3436, NewCertificates0107.C3437} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0107.C3438, NewCertificates0107.C3439, NewCertificates0107.C3440, NewCertificates0107.C3441, NewCertificates0107.C3442, NewCertificates0107.C3443, NewCertificates0107.C3444, NewCertificates0107.C3445} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0105.obstruction3390
  · exact NewCertificates0105.obstruction3391
  · exact NewCertificates0106.obstruction3392
  · exact NewCertificates0106.obstruction3393
  · exact NewCertificates0106.obstruction3394
  · exact NewCertificates0106.obstruction3395
  · exact NewCertificates0106.obstruction3396
  · exact NewCertificates0106.obstruction3397
  · exact NewCertificates0106.obstruction3398
  · exact NewCertificates0106.obstruction3399
  · exact NewCertificates0106.obstruction3400
  · exact NewCertificates0106.obstruction3401
  · exact NewCertificates0106.obstruction3402
  · exact NewCertificates0106.obstruction3403
  · exact NewCertificates0106.obstruction3404
  · exact NewCertificates0106.obstruction3405
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0106.obstruction3406
  · exact NewCertificates0106.obstruction3407
  · exact NewCertificates0106.obstruction3408
  · exact NewCertificates0106.obstruction3409
  · exact NewCertificates0106.obstruction3410
  · exact NewCertificates0106.obstruction3411
  · exact NewCertificates0106.obstruction3412
  · exact NewCertificates0106.obstruction3413
  · exact NewCertificates0106.obstruction3414
  · exact NewCertificates0106.obstruction3415
  · exact NewCertificates0106.obstruction3416
  · exact NewCertificates0106.obstruction3417
  · exact NewCertificates0106.obstruction3418
  · exact NewCertificates0106.obstruction3419
  · exact NewCertificates0106.obstruction3420
  · exact NewCertificates0106.obstruction3421
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0106.obstruction3422
  · exact NewCertificates0106.obstruction3423
  · exact NewCertificates0107.obstruction3424
  · exact NewCertificates0107.obstruction3425
  · exact NewCertificates0107.obstruction3426
  · exact NewCertificates0107.obstruction3427
  · exact NewCertificates0107.obstruction3428
  · exact NewCertificates0107.obstruction3429
  · exact NewCertificates0107.obstruction3430
  · exact NewCertificates0107.obstruction3431
  · exact NewCertificates0107.obstruction3432
  · exact NewCertificates0107.obstruction3433
  · exact NewCertificates0107.obstruction3434
  · exact NewCertificates0107.obstruction3435
  · exact NewCertificates0107.obstruction3436
  · exact NewCertificates0107.obstruction3437
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0107.obstruction3438
  · exact NewCertificates0107.obstruction3439
  · exact NewCertificates0107.obstruction3440
  · exact NewCertificates0107.obstruction3441
  · exact NewCertificates0107.obstruction3442
  · exact NewCertificates0107.obstruction3443
  · exact NewCertificates0107.obstruction3444
  · exact NewCertificates0107.obstruction3445
end Nut8.FiniteSupport071
