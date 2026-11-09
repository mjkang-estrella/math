import SupportData076
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport076
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0112.C3606, NewCertificates0112.C3607, NewCertificates0112.C3608, NewCertificates0112.C3609, NewCertificates0112.C3610, NewCertificates0112.C3611, NewCertificates0112.C3612, NewCertificates0112.C3613, NewCertificates0112.C3614, NewCertificates0112.C3615, NewCertificates0113.C3616, NewCertificates0113.C3617, NewCertificates0113.C3618, NewCertificates0113.C3619, NewCertificates0113.C3620, NewCertificates0113.C3621} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0113.C3622, NewCertificates0113.C3623, NewCertificates0113.C3624, NewCertificates0113.C3625, NewCertificates0113.C3626, NewCertificates0113.C3627, NewCertificates0113.C3628, NewCertificates0113.C3629, NewCertificates0113.C3630, NewCertificates0113.C3631, NewCertificates0113.C3632, NewCertificates0113.C3633, NewCertificates0113.C3634, NewCertificates0113.C3635, NewCertificates0113.C3636, NewCertificates0113.C3637} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0113.C3638, NewCertificates0113.C3639, NewCertificates0113.C3640, NewCertificates0113.C3641, NewCertificates0113.C3642, NewCertificates0113.C3643, NewCertificates0113.C3644, NewCertificates0113.C3645, NewCertificates0113.C3646, NewCertificates0113.C3647, NewCertificates0114.C3648, NewCertificates0114.C3649, NewCertificates0114.C3650, NewCertificates0114.C3651, NewCertificates0114.C3652, NewCertificates0114.C3653} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0112.obstruction3606
  · exact NewCertificates0112.obstruction3607
  · exact NewCertificates0112.obstruction3608
  · exact NewCertificates0112.obstruction3609
  · exact NewCertificates0112.obstruction3610
  · exact NewCertificates0112.obstruction3611
  · exact NewCertificates0112.obstruction3612
  · exact NewCertificates0112.obstruction3613
  · exact NewCertificates0112.obstruction3614
  · exact NewCertificates0112.obstruction3615
  · exact NewCertificates0113.obstruction3616
  · exact NewCertificates0113.obstruction3617
  · exact NewCertificates0113.obstruction3618
  · exact NewCertificates0113.obstruction3619
  · exact NewCertificates0113.obstruction3620
  · exact NewCertificates0113.obstruction3621
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0113.obstruction3622
  · exact NewCertificates0113.obstruction3623
  · exact NewCertificates0113.obstruction3624
  · exact NewCertificates0113.obstruction3625
  · exact NewCertificates0113.obstruction3626
  · exact NewCertificates0113.obstruction3627
  · exact NewCertificates0113.obstruction3628
  · exact NewCertificates0113.obstruction3629
  · exact NewCertificates0113.obstruction3630
  · exact NewCertificates0113.obstruction3631
  · exact NewCertificates0113.obstruction3632
  · exact NewCertificates0113.obstruction3633
  · exact NewCertificates0113.obstruction3634
  · exact NewCertificates0113.obstruction3635
  · exact NewCertificates0113.obstruction3636
  · exact NewCertificates0113.obstruction3637
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0113.obstruction3638
  · exact NewCertificates0113.obstruction3639
  · exact NewCertificates0113.obstruction3640
  · exact NewCertificates0113.obstruction3641
  · exact NewCertificates0113.obstruction3642
  · exact NewCertificates0113.obstruction3643
  · exact NewCertificates0113.obstruction3644
  · exact NewCertificates0113.obstruction3645
  · exact NewCertificates0113.obstruction3646
  · exact NewCertificates0113.obstruction3647
  · exact NewCertificates0114.obstruction3648
  · exact NewCertificates0114.obstruction3649
  · exact NewCertificates0114.obstruction3650
  · exact NewCertificates0114.obstruction3651
  · exact NewCertificates0114.obstruction3652
  · exact NewCertificates0114.obstruction3653
end Nut8.FiniteSupport076
