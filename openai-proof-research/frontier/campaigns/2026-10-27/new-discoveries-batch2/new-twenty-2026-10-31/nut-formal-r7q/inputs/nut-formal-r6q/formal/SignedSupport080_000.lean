import SupportData080
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport080
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0117.C3766, NewCertificates0117.C3767, NewCertificates0117.C3768, NewCertificates0117.C3769, NewCertificates0117.C3770, NewCertificates0117.C3771, NewCertificates0117.C3772, NewCertificates0117.C3773, NewCertificates0117.C3774, NewCertificates0117.C3775, NewCertificates0118.C3776, NewCertificates0118.C3777, NewCertificates0118.C3778, NewCertificates0118.C3779, NewCertificates0118.C3780, NewCertificates0118.C3781, NewCertificates0118.C3782, NewCertificates0118.C3783, NewCertificates0118.C3784, NewCertificates0118.C3785, NewCertificates0118.C3786, NewCertificates0118.C3787, NewCertificates0118.C3788, NewCertificates0118.C3789, NewCertificates0118.C3790, NewCertificates0118.C3791, NewCertificates0118.C3792, NewCertificates0118.C3793, NewCertificates0118.C3794, NewCertificates0118.C3795, NewCertificates0118.C3796, NewCertificates0118.C3797} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0117.obstruction3766
  · exact NewCertificates0117.obstruction3767
  · exact NewCertificates0117.obstruction3768
  · exact NewCertificates0117.obstruction3769
  · exact NewCertificates0117.obstruction3770
  · exact NewCertificates0117.obstruction3771
  · exact NewCertificates0117.obstruction3772
  · exact NewCertificates0117.obstruction3773
  · exact NewCertificates0117.obstruction3774
  · exact NewCertificates0117.obstruction3775
  · exact NewCertificates0118.obstruction3776
  · exact NewCertificates0118.obstruction3777
  · exact NewCertificates0118.obstruction3778
  · exact NewCertificates0118.obstruction3779
  · exact NewCertificates0118.obstruction3780
  · exact NewCertificates0118.obstruction3781
  · exact NewCertificates0118.obstruction3782
  · exact NewCertificates0118.obstruction3783
  · exact NewCertificates0118.obstruction3784
  · exact NewCertificates0118.obstruction3785
  · exact NewCertificates0118.obstruction3786
  · exact NewCertificates0118.obstruction3787
  · exact NewCertificates0118.obstruction3788
  · exact NewCertificates0118.obstruction3789
  · exact NewCertificates0118.obstruction3790
  · exact NewCertificates0118.obstruction3791
  · exact NewCertificates0118.obstruction3792
  · exact NewCertificates0118.obstruction3793
  · exact NewCertificates0118.obstruction3794
  · exact NewCertificates0118.obstruction3795
  · exact NewCertificates0118.obstruction3796
  · exact NewCertificates0118.obstruction3797
end Nut8.FiniteSupport080
