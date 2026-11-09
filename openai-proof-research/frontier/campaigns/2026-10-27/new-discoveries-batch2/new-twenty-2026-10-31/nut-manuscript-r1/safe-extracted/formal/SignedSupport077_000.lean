import SupportData077
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport077
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0114.C3654, NewCertificates0114.C3655, NewCertificates0114.C3656, NewCertificates0114.C3657, NewCertificates0114.C3658, NewCertificates0114.C3659, NewCertificates0114.C3660, NewCertificates0114.C3661, NewCertificates0114.C3662, NewCertificates0114.C3663, NewCertificates0114.C3664, NewCertificates0114.C3665, NewCertificates0114.C3666, NewCertificates0114.C3667, NewCertificates0114.C3668, NewCertificates0114.C3669, NewCertificates0114.C3670, NewCertificates0114.C3671, NewCertificates0114.C3672, NewCertificates0114.C3673, NewCertificates0114.C3674, NewCertificates0114.C3675, NewCertificates0114.C3676, NewCertificates0114.C3677, NewCertificates0114.C3678, NewCertificates0114.C3679, NewCertificates0115.C3680, NewCertificates0115.C3681, NewCertificates0115.C3682, NewCertificates0115.C3683, NewCertificates0115.C3684, NewCertificates0115.C3685} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0114.obstruction3654
  · exact NewCertificates0114.obstruction3655
  · exact NewCertificates0114.obstruction3656
  · exact NewCertificates0114.obstruction3657
  · exact NewCertificates0114.obstruction3658
  · exact NewCertificates0114.obstruction3659
  · exact NewCertificates0114.obstruction3660
  · exact NewCertificates0114.obstruction3661
  · exact NewCertificates0114.obstruction3662
  · exact NewCertificates0114.obstruction3663
  · exact NewCertificates0114.obstruction3664
  · exact NewCertificates0114.obstruction3665
  · exact NewCertificates0114.obstruction3666
  · exact NewCertificates0114.obstruction3667
  · exact NewCertificates0114.obstruction3668
  · exact NewCertificates0114.obstruction3669
  · exact NewCertificates0114.obstruction3670
  · exact NewCertificates0114.obstruction3671
  · exact NewCertificates0114.obstruction3672
  · exact NewCertificates0114.obstruction3673
  · exact NewCertificates0114.obstruction3674
  · exact NewCertificates0114.obstruction3675
  · exact NewCertificates0114.obstruction3676
  · exact NewCertificates0114.obstruction3677
  · exact NewCertificates0114.obstruction3678
  · exact NewCertificates0114.obstruction3679
  · exact NewCertificates0115.obstruction3680
  · exact NewCertificates0115.obstruction3681
  · exact NewCertificates0115.obstruction3682
  · exact NewCertificates0115.obstruction3683
  · exact NewCertificates0115.obstruction3684
  · exact NewCertificates0115.obstruction3685
end Nut8.FiniteSupport077
