import SupportData084
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport084
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0121.C3894, NewCertificates0121.C3895, NewCertificates0121.C3896, NewCertificates0121.C3897, NewCertificates0121.C3898, NewCertificates0121.C3899, NewCertificates0121.C3900, NewCertificates0121.C3901, NewCertificates0121.C3902, NewCertificates0121.C3903, NewCertificates0122.C3904, NewCertificates0122.C3905, NewCertificates0122.C3906, NewCertificates0122.C3907, NewCertificates0122.C3908, NewCertificates0122.C3909, NewCertificates0122.C3910, NewCertificates0122.C3911, NewCertificates0122.C3912, NewCertificates0122.C3913, NewCertificates0122.C3914, NewCertificates0122.C3915, NewCertificates0122.C3916, NewCertificates0122.C3917, NewCertificates0122.C3918, NewCertificates0122.C3919, NewCertificates0122.C3920, NewCertificates0122.C3921, NewCertificates0122.C3922, NewCertificates0122.C3923, NewCertificates0122.C3924, NewCertificates0122.C3925} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0121.obstruction3894
  · exact NewCertificates0121.obstruction3895
  · exact NewCertificates0121.obstruction3896
  · exact NewCertificates0121.obstruction3897
  · exact NewCertificates0121.obstruction3898
  · exact NewCertificates0121.obstruction3899
  · exact NewCertificates0121.obstruction3900
  · exact NewCertificates0121.obstruction3901
  · exact NewCertificates0121.obstruction3902
  · exact NewCertificates0121.obstruction3903
  · exact NewCertificates0122.obstruction3904
  · exact NewCertificates0122.obstruction3905
  · exact NewCertificates0122.obstruction3906
  · exact NewCertificates0122.obstruction3907
  · exact NewCertificates0122.obstruction3908
  · exact NewCertificates0122.obstruction3909
  · exact NewCertificates0122.obstruction3910
  · exact NewCertificates0122.obstruction3911
  · exact NewCertificates0122.obstruction3912
  · exact NewCertificates0122.obstruction3913
  · exact NewCertificates0122.obstruction3914
  · exact NewCertificates0122.obstruction3915
  · exact NewCertificates0122.obstruction3916
  · exact NewCertificates0122.obstruction3917
  · exact NewCertificates0122.obstruction3918
  · exact NewCertificates0122.obstruction3919
  · exact NewCertificates0122.obstruction3920
  · exact NewCertificates0122.obstruction3921
  · exact NewCertificates0122.obstruction3922
  · exact NewCertificates0122.obstruction3923
  · exact NewCertificates0122.obstruction3924
  · exact NewCertificates0122.obstruction3925
end Nut8.FiniteSupport084
