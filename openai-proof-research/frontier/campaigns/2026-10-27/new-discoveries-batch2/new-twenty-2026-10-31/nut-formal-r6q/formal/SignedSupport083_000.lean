import SupportData083
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport083
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0120.C3862, NewCertificates0120.C3863, NewCertificates0120.C3864, NewCertificates0120.C3865, NewCertificates0120.C3866, NewCertificates0120.C3867, NewCertificates0120.C3868, NewCertificates0120.C3869, NewCertificates0120.C3870, NewCertificates0120.C3871, NewCertificates0121.C3872, NewCertificates0121.C3873, NewCertificates0121.C3874, NewCertificates0121.C3875, NewCertificates0121.C3876, NewCertificates0121.C3877, NewCertificates0121.C3878, NewCertificates0121.C3879, NewCertificates0121.C3880, NewCertificates0121.C3881, NewCertificates0121.C3882, NewCertificates0121.C3883, NewCertificates0121.C3884, NewCertificates0121.C3885, NewCertificates0121.C3886, NewCertificates0121.C3887, NewCertificates0121.C3888, NewCertificates0121.C3889, NewCertificates0121.C3890, NewCertificates0121.C3891, NewCertificates0121.C3892, NewCertificates0121.C3893} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0120.obstruction3862
  · exact NewCertificates0120.obstruction3863
  · exact NewCertificates0120.obstruction3864
  · exact NewCertificates0120.obstruction3865
  · exact NewCertificates0120.obstruction3866
  · exact NewCertificates0120.obstruction3867
  · exact NewCertificates0120.obstruction3868
  · exact NewCertificates0120.obstruction3869
  · exact NewCertificates0120.obstruction3870
  · exact NewCertificates0120.obstruction3871
  · exact NewCertificates0121.obstruction3872
  · exact NewCertificates0121.obstruction3873
  · exact NewCertificates0121.obstruction3874
  · exact NewCertificates0121.obstruction3875
  · exact NewCertificates0121.obstruction3876
  · exact NewCertificates0121.obstruction3877
  · exact NewCertificates0121.obstruction3878
  · exact NewCertificates0121.obstruction3879
  · exact NewCertificates0121.obstruction3880
  · exact NewCertificates0121.obstruction3881
  · exact NewCertificates0121.obstruction3882
  · exact NewCertificates0121.obstruction3883
  · exact NewCertificates0121.obstruction3884
  · exact NewCertificates0121.obstruction3885
  · exact NewCertificates0121.obstruction3886
  · exact NewCertificates0121.obstruction3887
  · exact NewCertificates0121.obstruction3888
  · exact NewCertificates0121.obstruction3889
  · exact NewCertificates0121.obstruction3890
  · exact NewCertificates0121.obstruction3891
  · exact NewCertificates0121.obstruction3892
  · exact NewCertificates0121.obstruction3893
end Nut8.FiniteSupport083
