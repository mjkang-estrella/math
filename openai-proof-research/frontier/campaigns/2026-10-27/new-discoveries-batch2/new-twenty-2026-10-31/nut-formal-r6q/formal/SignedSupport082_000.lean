import SupportData082
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport082
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0119.C3830, NewCertificates0119.C3831, NewCertificates0119.C3832, NewCertificates0119.C3833, NewCertificates0119.C3834, NewCertificates0119.C3835, NewCertificates0119.C3836, NewCertificates0119.C3837, NewCertificates0119.C3838, NewCertificates0119.C3839, NewCertificates0120.C3840, NewCertificates0120.C3841, NewCertificates0120.C3842, NewCertificates0120.C3843, NewCertificates0120.C3844, NewCertificates0120.C3845, NewCertificates0120.C3846, NewCertificates0120.C3847, NewCertificates0120.C3848, NewCertificates0120.C3849, NewCertificates0120.C3850, NewCertificates0120.C3851, NewCertificates0120.C3852, NewCertificates0120.C3853, NewCertificates0120.C3854, NewCertificates0120.C3855, NewCertificates0120.C3856, NewCertificates0120.C3857, NewCertificates0120.C3858, NewCertificates0120.C3859, NewCertificates0120.C3860, NewCertificates0120.C3861} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0119.obstruction3830
  · exact NewCertificates0119.obstruction3831
  · exact NewCertificates0119.obstruction3832
  · exact NewCertificates0119.obstruction3833
  · exact NewCertificates0119.obstruction3834
  · exact NewCertificates0119.obstruction3835
  · exact NewCertificates0119.obstruction3836
  · exact NewCertificates0119.obstruction3837
  · exact NewCertificates0119.obstruction3838
  · exact NewCertificates0119.obstruction3839
  · exact NewCertificates0120.obstruction3840
  · exact NewCertificates0120.obstruction3841
  · exact NewCertificates0120.obstruction3842
  · exact NewCertificates0120.obstruction3843
  · exact NewCertificates0120.obstruction3844
  · exact NewCertificates0120.obstruction3845
  · exact NewCertificates0120.obstruction3846
  · exact NewCertificates0120.obstruction3847
  · exact NewCertificates0120.obstruction3848
  · exact NewCertificates0120.obstruction3849
  · exact NewCertificates0120.obstruction3850
  · exact NewCertificates0120.obstruction3851
  · exact NewCertificates0120.obstruction3852
  · exact NewCertificates0120.obstruction3853
  · exact NewCertificates0120.obstruction3854
  · exact NewCertificates0120.obstruction3855
  · exact NewCertificates0120.obstruction3856
  · exact NewCertificates0120.obstruction3857
  · exact NewCertificates0120.obstruction3858
  · exact NewCertificates0120.obstruction3859
  · exact NewCertificates0120.obstruction3860
  · exact NewCertificates0120.obstruction3861
end Nut8.FiniteSupport082
