import SupportData079
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport079
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0116.C3734, NewCertificates0116.C3735, NewCertificates0116.C3736, NewCertificates0116.C3737, NewCertificates0116.C3738, NewCertificates0116.C3739, NewCertificates0116.C3740, NewCertificates0116.C3741, NewCertificates0116.C3742, NewCertificates0116.C3743, NewCertificates0117.C3744, NewCertificates0117.C3745, NewCertificates0117.C3746, NewCertificates0117.C3747, NewCertificates0117.C3748, NewCertificates0117.C3749, NewCertificates0117.C3750, NewCertificates0117.C3751, NewCertificates0117.C3752, NewCertificates0117.C3753, NewCertificates0117.C3754, NewCertificates0117.C3755, NewCertificates0117.C3756, NewCertificates0117.C3757, NewCertificates0117.C3758, NewCertificates0117.C3759, NewCertificates0117.C3760, NewCertificates0117.C3761, NewCertificates0117.C3762, NewCertificates0117.C3763, NewCertificates0117.C3764, NewCertificates0117.C3765} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0116.obstruction3734
  · exact NewCertificates0116.obstruction3735
  · exact NewCertificates0116.obstruction3736
  · exact NewCertificates0116.obstruction3737
  · exact NewCertificates0116.obstruction3738
  · exact NewCertificates0116.obstruction3739
  · exact NewCertificates0116.obstruction3740
  · exact NewCertificates0116.obstruction3741
  · exact NewCertificates0116.obstruction3742
  · exact NewCertificates0116.obstruction3743
  · exact NewCertificates0117.obstruction3744
  · exact NewCertificates0117.obstruction3745
  · exact NewCertificates0117.obstruction3746
  · exact NewCertificates0117.obstruction3747
  · exact NewCertificates0117.obstruction3748
  · exact NewCertificates0117.obstruction3749
  · exact NewCertificates0117.obstruction3750
  · exact NewCertificates0117.obstruction3751
  · exact NewCertificates0117.obstruction3752
  · exact NewCertificates0117.obstruction3753
  · exact NewCertificates0117.obstruction3754
  · exact NewCertificates0117.obstruction3755
  · exact NewCertificates0117.obstruction3756
  · exact NewCertificates0117.obstruction3757
  · exact NewCertificates0117.obstruction3758
  · exact NewCertificates0117.obstruction3759
  · exact NewCertificates0117.obstruction3760
  · exact NewCertificates0117.obstruction3761
  · exact NewCertificates0117.obstruction3762
  · exact NewCertificates0117.obstruction3763
  · exact NewCertificates0117.obstruction3764
  · exact NewCertificates0117.obstruction3765
end Nut8.FiniteSupport079
