import SupportData073
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport073
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0109.C3494, NewCertificates0109.C3495, NewCertificates0109.C3496, NewCertificates0109.C3497, NewCertificates0109.C3498, NewCertificates0109.C3499, NewCertificates0109.C3500, NewCertificates0109.C3501, NewCertificates0109.C3502, NewCertificates0109.C3503, NewCertificates0109.C3504, NewCertificates0109.C3505, NewCertificates0109.C3506, NewCertificates0109.C3507, NewCertificates0109.C3508, NewCertificates0109.C3509} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0109.C3510, NewCertificates0109.C3511, NewCertificates0109.C3512, NewCertificates0109.C3513, NewCertificates0109.C3514, NewCertificates0109.C3515, NewCertificates0109.C3516, NewCertificates0109.C3517, NewCertificates0109.C3518, NewCertificates0109.C3519, NewCertificates0110.C3520, NewCertificates0110.C3521, NewCertificates0110.C3522, NewCertificates0110.C3523, NewCertificates0110.C3524, NewCertificates0110.C3525} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0110.C3526, NewCertificates0110.C3527, NewCertificates0110.C3528, NewCertificates0110.C3529, NewCertificates0110.C3530, NewCertificates0110.C3531, NewCertificates0110.C3532, NewCertificates0110.C3533, NewCertificates0110.C3534, NewCertificates0110.C3535, NewCertificates0110.C3536, NewCertificates0110.C3537, NewCertificates0110.C3538, NewCertificates0110.C3539, NewCertificates0110.C3540, NewCertificates0110.C3541} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0109.obstruction3494
  · exact NewCertificates0109.obstruction3495
  · exact NewCertificates0109.obstruction3496
  · exact NewCertificates0109.obstruction3497
  · exact NewCertificates0109.obstruction3498
  · exact NewCertificates0109.obstruction3499
  · exact NewCertificates0109.obstruction3500
  · exact NewCertificates0109.obstruction3501
  · exact NewCertificates0109.obstruction3502
  · exact NewCertificates0109.obstruction3503
  · exact NewCertificates0109.obstruction3504
  · exact NewCertificates0109.obstruction3505
  · exact NewCertificates0109.obstruction3506
  · exact NewCertificates0109.obstruction3507
  · exact NewCertificates0109.obstruction3508
  · exact NewCertificates0109.obstruction3509
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0109.obstruction3510
  · exact NewCertificates0109.obstruction3511
  · exact NewCertificates0109.obstruction3512
  · exact NewCertificates0109.obstruction3513
  · exact NewCertificates0109.obstruction3514
  · exact NewCertificates0109.obstruction3515
  · exact NewCertificates0109.obstruction3516
  · exact NewCertificates0109.obstruction3517
  · exact NewCertificates0109.obstruction3518
  · exact NewCertificates0109.obstruction3519
  · exact NewCertificates0110.obstruction3520
  · exact NewCertificates0110.obstruction3521
  · exact NewCertificates0110.obstruction3522
  · exact NewCertificates0110.obstruction3523
  · exact NewCertificates0110.obstruction3524
  · exact NewCertificates0110.obstruction3525
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0110.obstruction3526
  · exact NewCertificates0110.obstruction3527
  · exact NewCertificates0110.obstruction3528
  · exact NewCertificates0110.obstruction3529
  · exact NewCertificates0110.obstruction3530
  · exact NewCertificates0110.obstruction3531
  · exact NewCertificates0110.obstruction3532
  · exact NewCertificates0110.obstruction3533
  · exact NewCertificates0110.obstruction3534
  · exact NewCertificates0110.obstruction3535
  · exact NewCertificates0110.obstruction3536
  · exact NewCertificates0110.obstruction3537
  · exact NewCertificates0110.obstruction3538
  · exact NewCertificates0110.obstruction3539
  · exact NewCertificates0110.obstruction3540
  · exact NewCertificates0110.obstruction3541
end Nut8.FiniteSupport073
