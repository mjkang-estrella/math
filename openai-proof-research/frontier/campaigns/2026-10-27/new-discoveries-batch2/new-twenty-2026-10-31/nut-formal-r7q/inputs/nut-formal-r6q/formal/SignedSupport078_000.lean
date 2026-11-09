import SupportData078
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport078
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0115.C3686, NewCertificates0115.C3687, NewCertificates0115.C3688, NewCertificates0115.C3689, NewCertificates0115.C3690, NewCertificates0115.C3691, NewCertificates0115.C3692, NewCertificates0115.C3693, NewCertificates0115.C3694, NewCertificates0115.C3695, NewCertificates0115.C3696, NewCertificates0115.C3697, NewCertificates0115.C3698, NewCertificates0115.C3699, NewCertificates0115.C3700, NewCertificates0115.C3701} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0115.C3702, NewCertificates0115.C3703, NewCertificates0115.C3704, NewCertificates0115.C3705, NewCertificates0115.C3706, NewCertificates0115.C3707, NewCertificates0115.C3708, NewCertificates0115.C3709, NewCertificates0115.C3710, NewCertificates0115.C3711, NewCertificates0116.C3712, NewCertificates0116.C3713, NewCertificates0116.C3714, NewCertificates0116.C3715, NewCertificates0116.C3716, NewCertificates0116.C3717} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0116.C3718, NewCertificates0116.C3719, NewCertificates0116.C3720, NewCertificates0116.C3721, NewCertificates0116.C3722, NewCertificates0116.C3723, NewCertificates0116.C3724, NewCertificates0116.C3725, NewCertificates0116.C3726, NewCertificates0116.C3727, NewCertificates0116.C3728, NewCertificates0116.C3729, NewCertificates0116.C3730, NewCertificates0116.C3731, NewCertificates0116.C3732, NewCertificates0116.C3733} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0115.obstruction3686
  · exact NewCertificates0115.obstruction3687
  · exact NewCertificates0115.obstruction3688
  · exact NewCertificates0115.obstruction3689
  · exact NewCertificates0115.obstruction3690
  · exact NewCertificates0115.obstruction3691
  · exact NewCertificates0115.obstruction3692
  · exact NewCertificates0115.obstruction3693
  · exact NewCertificates0115.obstruction3694
  · exact NewCertificates0115.obstruction3695
  · exact NewCertificates0115.obstruction3696
  · exact NewCertificates0115.obstruction3697
  · exact NewCertificates0115.obstruction3698
  · exact NewCertificates0115.obstruction3699
  · exact NewCertificates0115.obstruction3700
  · exact NewCertificates0115.obstruction3701
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0115.obstruction3702
  · exact NewCertificates0115.obstruction3703
  · exact NewCertificates0115.obstruction3704
  · exact NewCertificates0115.obstruction3705
  · exact NewCertificates0115.obstruction3706
  · exact NewCertificates0115.obstruction3707
  · exact NewCertificates0115.obstruction3708
  · exact NewCertificates0115.obstruction3709
  · exact NewCertificates0115.obstruction3710
  · exact NewCertificates0115.obstruction3711
  · exact NewCertificates0116.obstruction3712
  · exact NewCertificates0116.obstruction3713
  · exact NewCertificates0116.obstruction3714
  · exact NewCertificates0116.obstruction3715
  · exact NewCertificates0116.obstruction3716
  · exact NewCertificates0116.obstruction3717
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0116.obstruction3718
  · exact NewCertificates0116.obstruction3719
  · exact NewCertificates0116.obstruction3720
  · exact NewCertificates0116.obstruction3721
  · exact NewCertificates0116.obstruction3722
  · exact NewCertificates0116.obstruction3723
  · exact NewCertificates0116.obstruction3724
  · exact NewCertificates0116.obstruction3725
  · exact NewCertificates0116.obstruction3726
  · exact NewCertificates0116.obstruction3727
  · exact NewCertificates0116.obstruction3728
  · exact NewCertificates0116.obstruction3729
  · exact NewCertificates0116.obstruction3730
  · exact NewCertificates0116.obstruction3731
  · exact NewCertificates0116.obstruction3732
  · exact NewCertificates0116.obstruction3733
end Nut8.FiniteSupport078
