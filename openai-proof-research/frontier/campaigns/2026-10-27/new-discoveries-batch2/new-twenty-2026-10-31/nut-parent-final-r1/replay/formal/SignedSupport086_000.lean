import SupportData086
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport086
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0123.C3958, NewCertificates0123.C3959, NewCertificates0123.C3960, NewCertificates0123.C3961, NewCertificates0123.C3962, NewCertificates0123.C3963, NewCertificates0123.C3964, NewCertificates0123.C3965, NewCertificates0123.C3966, NewCertificates0123.C3967, NewCertificates0124.C3968, NewCertificates0124.C3969, NewCertificates0124.C3970, NewCertificates0124.C3971, NewCertificates0124.C3972, NewCertificates0124.C3973, NewCertificates0124.C3974, NewCertificates0124.C3975, NewCertificates0124.C3976, NewCertificates0124.C3977, NewCertificates0124.C3978, NewCertificates0124.C3979, NewCertificates0124.C3980, NewCertificates0124.C3981, NewCertificates0124.C3982, NewCertificates0124.C3983, NewCertificates0124.C3984, NewCertificates0124.C3985, NewCertificates0124.C3986, NewCertificates0124.C3987, NewCertificates0124.C3988, NewCertificates0124.C3989} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0124.C3990, NewCertificates0124.C3991, NewCertificates0124.C3992, NewCertificates0124.C3993, NewCertificates0124.C3994, NewCertificates0124.C3995, NewCertificates0124.C3996, NewCertificates0124.C3997, NewCertificates0124.C3998, NewCertificates0124.C3999, NewCertificates0125.C4000, NewCertificates0125.C4001, NewCertificates0125.C4002, NewCertificates0125.C4003, NewCertificates0125.C4004, NewCertificates0125.C4005} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0125.C4006, NewCertificates0125.C4007, NewCertificates0125.C4008, NewCertificates0125.C4009, NewCertificates0125.C4010, NewCertificates0125.C4011, NewCertificates0125.C4012, NewCertificates0125.C4013, NewCertificates0125.C4014, NewCertificates0125.C4015, NewCertificates0125.C4016, NewCertificates0125.C4017, NewCertificates0125.C4018, NewCertificates0125.C4019, NewCertificates0125.C4020, NewCertificates0125.C4021} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0125.C4022, NewCertificates0125.C4023, NewCertificates0125.C4024, NewCertificates0125.C4025, NewCertificates0125.C4026, NewCertificates0125.C4027, NewCertificates0125.C4028, NewCertificates0125.C4029} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0123.obstruction3958
  · exact NewCertificates0123.obstruction3959
  · exact NewCertificates0123.obstruction3960
  · exact NewCertificates0123.obstruction3961
  · exact NewCertificates0123.obstruction3962
  · exact NewCertificates0123.obstruction3963
  · exact NewCertificates0123.obstruction3964
  · exact NewCertificates0123.obstruction3965
  · exact NewCertificates0123.obstruction3966
  · exact NewCertificates0123.obstruction3967
  · exact NewCertificates0124.obstruction3968
  · exact NewCertificates0124.obstruction3969
  · exact NewCertificates0124.obstruction3970
  · exact NewCertificates0124.obstruction3971
  · exact NewCertificates0124.obstruction3972
  · exact NewCertificates0124.obstruction3973
  · exact NewCertificates0124.obstruction3974
  · exact NewCertificates0124.obstruction3975
  · exact NewCertificates0124.obstruction3976
  · exact NewCertificates0124.obstruction3977
  · exact NewCertificates0124.obstruction3978
  · exact NewCertificates0124.obstruction3979
  · exact NewCertificates0124.obstruction3980
  · exact NewCertificates0124.obstruction3981
  · exact NewCertificates0124.obstruction3982
  · exact NewCertificates0124.obstruction3983
  · exact NewCertificates0124.obstruction3984
  · exact NewCertificates0124.obstruction3985
  · exact NewCertificates0124.obstruction3986
  · exact NewCertificates0124.obstruction3987
  · exact NewCertificates0124.obstruction3988
  · exact NewCertificates0124.obstruction3989
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0124.obstruction3990
  · exact NewCertificates0124.obstruction3991
  · exact NewCertificates0124.obstruction3992
  · exact NewCertificates0124.obstruction3993
  · exact NewCertificates0124.obstruction3994
  · exact NewCertificates0124.obstruction3995
  · exact NewCertificates0124.obstruction3996
  · exact NewCertificates0124.obstruction3997
  · exact NewCertificates0124.obstruction3998
  · exact NewCertificates0124.obstruction3999
  · exact NewCertificates0125.obstruction4000
  · exact NewCertificates0125.obstruction4001
  · exact NewCertificates0125.obstruction4002
  · exact NewCertificates0125.obstruction4003
  · exact NewCertificates0125.obstruction4004
  · exact NewCertificates0125.obstruction4005
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0125.obstruction4006
  · exact NewCertificates0125.obstruction4007
  · exact NewCertificates0125.obstruction4008
  · exact NewCertificates0125.obstruction4009
  · exact NewCertificates0125.obstruction4010
  · exact NewCertificates0125.obstruction4011
  · exact NewCertificates0125.obstruction4012
  · exact NewCertificates0125.obstruction4013
  · exact NewCertificates0125.obstruction4014
  · exact NewCertificates0125.obstruction4015
  · exact NewCertificates0125.obstruction4016
  · exact NewCertificates0125.obstruction4017
  · exact NewCertificates0125.obstruction4018
  · exact NewCertificates0125.obstruction4019
  · exact NewCertificates0125.obstruction4020
  · exact NewCertificates0125.obstruction4021
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0125.obstruction4022
  · exact NewCertificates0125.obstruction4023
  · exact NewCertificates0125.obstruction4024
  · exact NewCertificates0125.obstruction4025
  · exact NewCertificates0125.obstruction4026
  · exact NewCertificates0125.obstruction4027
  · exact NewCertificates0125.obstruction4028
  · exact NewCertificates0125.obstruction4029
end Nut8.FiniteSupport086
