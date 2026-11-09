import SupportData081
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport081
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0118.C3798, NewCertificates0118.C3799, NewCertificates0118.C3800, NewCertificates0118.C3801, NewCertificates0118.C3802, NewCertificates0118.C3803, NewCertificates0118.C3804, NewCertificates0118.C3805, NewCertificates0118.C3806, NewCertificates0118.C3807, NewCertificates0119.C3808, NewCertificates0119.C3809, NewCertificates0119.C3810, NewCertificates0119.C3811, NewCertificates0119.C3812, NewCertificates0119.C3813, NewCertificates0119.C3814, NewCertificates0119.C3815, NewCertificates0119.C3816, NewCertificates0119.C3817, NewCertificates0119.C3818, NewCertificates0119.C3819, NewCertificates0119.C3820, NewCertificates0119.C3821, NewCertificates0119.C3822, NewCertificates0119.C3823, NewCertificates0119.C3824, NewCertificates0119.C3825, NewCertificates0119.C3826, NewCertificates0119.C3827, NewCertificates0119.C3828, NewCertificates0119.C3829} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0118.obstruction3798
  · exact NewCertificates0118.obstruction3799
  · exact NewCertificates0118.obstruction3800
  · exact NewCertificates0118.obstruction3801
  · exact NewCertificates0118.obstruction3802
  · exact NewCertificates0118.obstruction3803
  · exact NewCertificates0118.obstruction3804
  · exact NewCertificates0118.obstruction3805
  · exact NewCertificates0118.obstruction3806
  · exact NewCertificates0118.obstruction3807
  · exact NewCertificates0119.obstruction3808
  · exact NewCertificates0119.obstruction3809
  · exact NewCertificates0119.obstruction3810
  · exact NewCertificates0119.obstruction3811
  · exact NewCertificates0119.obstruction3812
  · exact NewCertificates0119.obstruction3813
  · exact NewCertificates0119.obstruction3814
  · exact NewCertificates0119.obstruction3815
  · exact NewCertificates0119.obstruction3816
  · exact NewCertificates0119.obstruction3817
  · exact NewCertificates0119.obstruction3818
  · exact NewCertificates0119.obstruction3819
  · exact NewCertificates0119.obstruction3820
  · exact NewCertificates0119.obstruction3821
  · exact NewCertificates0119.obstruction3822
  · exact NewCertificates0119.obstruction3823
  · exact NewCertificates0119.obstruction3824
  · exact NewCertificates0119.obstruction3825
  · exact NewCertificates0119.obstruction3826
  · exact NewCertificates0119.obstruction3827
  · exact NewCertificates0119.obstruction3828
  · exact NewCertificates0119.obstruction3829
end Nut8.FiniteSupport081
