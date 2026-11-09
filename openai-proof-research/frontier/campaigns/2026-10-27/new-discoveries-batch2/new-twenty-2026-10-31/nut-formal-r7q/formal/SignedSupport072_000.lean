import SupportData072
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport072
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0108.C3462, NewCertificates0108.C3463, NewCertificates0108.C3464, NewCertificates0108.C3465, NewCertificates0108.C3466, NewCertificates0108.C3467, NewCertificates0108.C3468, NewCertificates0108.C3469, NewCertificates0108.C3470, NewCertificates0108.C3471, NewCertificates0108.C3472, NewCertificates0108.C3473, NewCertificates0108.C3474, NewCertificates0108.C3475, NewCertificates0108.C3476, NewCertificates0108.C3477} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0108.C3478, NewCertificates0108.C3479, NewCertificates0108.C3480, NewCertificates0108.C3481, NewCertificates0108.C3482, NewCertificates0108.C3483, NewCertificates0108.C3484, NewCertificates0108.C3485, NewCertificates0108.C3486, NewCertificates0108.C3487, NewCertificates0109.C3488, NewCertificates0109.C3489, NewCertificates0109.C3490, NewCertificates0109.C3491, NewCertificates0109.C3492, NewCertificates0109.C3493} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0108.obstruction3462
  · exact NewCertificates0108.obstruction3463
  · exact NewCertificates0108.obstruction3464
  · exact NewCertificates0108.obstruction3465
  · exact NewCertificates0108.obstruction3466
  · exact NewCertificates0108.obstruction3467
  · exact NewCertificates0108.obstruction3468
  · exact NewCertificates0108.obstruction3469
  · exact NewCertificates0108.obstruction3470
  · exact NewCertificates0108.obstruction3471
  · exact NewCertificates0108.obstruction3472
  · exact NewCertificates0108.obstruction3473
  · exact NewCertificates0108.obstruction3474
  · exact NewCertificates0108.obstruction3475
  · exact NewCertificates0108.obstruction3476
  · exact NewCertificates0108.obstruction3477
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0108.obstruction3478
  · exact NewCertificates0108.obstruction3479
  · exact NewCertificates0108.obstruction3480
  · exact NewCertificates0108.obstruction3481
  · exact NewCertificates0108.obstruction3482
  · exact NewCertificates0108.obstruction3483
  · exact NewCertificates0108.obstruction3484
  · exact NewCertificates0108.obstruction3485
  · exact NewCertificates0108.obstruction3486
  · exact NewCertificates0108.obstruction3487
  · exact NewCertificates0109.obstruction3488
  · exact NewCertificates0109.obstruction3489
  · exact NewCertificates0109.obstruction3490
  · exact NewCertificates0109.obstruction3491
  · exact NewCertificates0109.obstruction3492
  · exact NewCertificates0109.obstruction3493
end Nut8.FiniteSupport072
