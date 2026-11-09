import SupportData087
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport087
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0125.C4030, NewCertificates0125.C4031, NewCertificates0126.C4032, NewCertificates0126.C4033, NewCertificates0126.C4034, NewCertificates0126.C4035, NewCertificates0126.C4036, NewCertificates0126.C4037, NewCertificates0126.C4038, NewCertificates0126.C4039, NewCertificates0126.C4040, NewCertificates0126.C4041, NewCertificates0126.C4042, NewCertificates0126.C4043, NewCertificates0126.C4044, NewCertificates0126.C4045, NewCertificates0126.C4046, NewCertificates0126.C4047, NewCertificates0126.C4048, NewCertificates0126.C4049, NewCertificates0126.C4050, NewCertificates0126.C4051, NewCertificates0126.C4052, NewCertificates0126.C4053, NewCertificates0126.C4054, NewCertificates0126.C4055, NewCertificates0126.C4056, NewCertificates0126.C4057, NewCertificates0126.C4058, NewCertificates0126.C4059, NewCertificates0126.C4060, NewCertificates0126.C4061} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0125.obstruction4030
  · exact NewCertificates0125.obstruction4031
  · exact NewCertificates0126.obstruction4032
  · exact NewCertificates0126.obstruction4033
  · exact NewCertificates0126.obstruction4034
  · exact NewCertificates0126.obstruction4035
  · exact NewCertificates0126.obstruction4036
  · exact NewCertificates0126.obstruction4037
  · exact NewCertificates0126.obstruction4038
  · exact NewCertificates0126.obstruction4039
  · exact NewCertificates0126.obstruction4040
  · exact NewCertificates0126.obstruction4041
  · exact NewCertificates0126.obstruction4042
  · exact NewCertificates0126.obstruction4043
  · exact NewCertificates0126.obstruction4044
  · exact NewCertificates0126.obstruction4045
  · exact NewCertificates0126.obstruction4046
  · exact NewCertificates0126.obstruction4047
  · exact NewCertificates0126.obstruction4048
  · exact NewCertificates0126.obstruction4049
  · exact NewCertificates0126.obstruction4050
  · exact NewCertificates0126.obstruction4051
  · exact NewCertificates0126.obstruction4052
  · exact NewCertificates0126.obstruction4053
  · exact NewCertificates0126.obstruction4054
  · exact NewCertificates0126.obstruction4055
  · exact NewCertificates0126.obstruction4056
  · exact NewCertificates0126.obstruction4057
  · exact NewCertificates0126.obstruction4058
  · exact NewCertificates0126.obstruction4059
  · exact NewCertificates0126.obstruction4060
  · exact NewCertificates0126.obstruction4061
end Nut8.FiniteSupport087
