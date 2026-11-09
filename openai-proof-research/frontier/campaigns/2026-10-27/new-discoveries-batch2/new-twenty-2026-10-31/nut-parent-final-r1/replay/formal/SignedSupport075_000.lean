import SupportData075
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport075
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0111.C3574, NewCertificates0111.C3575, NewCertificates0111.C3576, NewCertificates0111.C3577, NewCertificates0111.C3578, NewCertificates0111.C3579, NewCertificates0111.C3580, NewCertificates0111.C3581, NewCertificates0111.C3582, NewCertificates0111.C3583, NewCertificates0112.C3584, NewCertificates0112.C3585, NewCertificates0112.C3586, NewCertificates0112.C3587, NewCertificates0112.C3588, NewCertificates0112.C3589, NewCertificates0112.C3590, NewCertificates0112.C3591, NewCertificates0112.C3592, NewCertificates0112.C3593, NewCertificates0112.C3594, NewCertificates0112.C3595, NewCertificates0112.C3596, NewCertificates0112.C3597, NewCertificates0112.C3598, NewCertificates0112.C3599, NewCertificates0112.C3600, NewCertificates0112.C3601, NewCertificates0112.C3602, NewCertificates0112.C3603, NewCertificates0112.C3604, NewCertificates0112.C3605} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0111.obstruction3574
  · exact NewCertificates0111.obstruction3575
  · exact NewCertificates0111.obstruction3576
  · exact NewCertificates0111.obstruction3577
  · exact NewCertificates0111.obstruction3578
  · exact NewCertificates0111.obstruction3579
  · exact NewCertificates0111.obstruction3580
  · exact NewCertificates0111.obstruction3581
  · exact NewCertificates0111.obstruction3582
  · exact NewCertificates0111.obstruction3583
  · exact NewCertificates0112.obstruction3584
  · exact NewCertificates0112.obstruction3585
  · exact NewCertificates0112.obstruction3586
  · exact NewCertificates0112.obstruction3587
  · exact NewCertificates0112.obstruction3588
  · exact NewCertificates0112.obstruction3589
  · exact NewCertificates0112.obstruction3590
  · exact NewCertificates0112.obstruction3591
  · exact NewCertificates0112.obstruction3592
  · exact NewCertificates0112.obstruction3593
  · exact NewCertificates0112.obstruction3594
  · exact NewCertificates0112.obstruction3595
  · exact NewCertificates0112.obstruction3596
  · exact NewCertificates0112.obstruction3597
  · exact NewCertificates0112.obstruction3598
  · exact NewCertificates0112.obstruction3599
  · exact NewCertificates0112.obstruction3600
  · exact NewCertificates0112.obstruction3601
  · exact NewCertificates0112.obstruction3602
  · exact NewCertificates0112.obstruction3603
  · exact NewCertificates0112.obstruction3604
  · exact NewCertificates0112.obstruction3605
end Nut8.FiniteSupport075
