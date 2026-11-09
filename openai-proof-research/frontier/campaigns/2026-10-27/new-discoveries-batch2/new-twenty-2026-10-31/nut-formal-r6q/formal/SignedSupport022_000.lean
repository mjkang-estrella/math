import SupportData022
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport022
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0032.C1032, NewCertificates0032.C1033, NewCertificates0032.C1034, NewCertificates0032.C1035, NewCertificates0032.C1036, NewCertificates0032.C1037, NewCertificates0032.C1038, NewCertificates0032.C1039, NewCertificates0032.C1040, NewCertificates0032.C1041, NewCertificates0032.C1042, NewCertificates0032.C1043, NewCertificates0032.C1044, NewCertificates0032.C1045, NewCertificates0032.C1046, NewCertificates0032.C1047, NewCertificates0032.C1048, NewCertificates0032.C1049, NewCertificates0032.C1050, NewCertificates0032.C1051, NewCertificates0032.C1052, NewCertificates0032.C1053, NewCertificates0032.C1054, NewCertificates0032.C1055, NewCertificates0033.C1056, NewCertificates0033.C1057, NewCertificates0033.C1058, NewCertificates0033.C1059, NewCertificates0033.C1060, NewCertificates0033.C1061, NewCertificates0033.C1062, NewCertificates0033.C1063} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0032.obstruction1032
  · exact NewCertificates0032.obstruction1033
  · exact NewCertificates0032.obstruction1034
  · exact NewCertificates0032.obstruction1035
  · exact NewCertificates0032.obstruction1036
  · exact NewCertificates0032.obstruction1037
  · exact NewCertificates0032.obstruction1038
  · exact NewCertificates0032.obstruction1039
  · exact NewCertificates0032.obstruction1040
  · exact NewCertificates0032.obstruction1041
  · exact NewCertificates0032.obstruction1042
  · exact NewCertificates0032.obstruction1043
  · exact NewCertificates0032.obstruction1044
  · exact NewCertificates0032.obstruction1045
  · exact NewCertificates0032.obstruction1046
  · exact NewCertificates0032.obstruction1047
  · exact NewCertificates0032.obstruction1048
  · exact NewCertificates0032.obstruction1049
  · exact NewCertificates0032.obstruction1050
  · exact NewCertificates0032.obstruction1051
  · exact NewCertificates0032.obstruction1052
  · exact NewCertificates0032.obstruction1053
  · exact NewCertificates0032.obstruction1054
  · exact NewCertificates0032.obstruction1055
  · exact NewCertificates0033.obstruction1056
  · exact NewCertificates0033.obstruction1057
  · exact NewCertificates0033.obstruction1058
  · exact NewCertificates0033.obstruction1059
  · exact NewCertificates0033.obstruction1060
  · exact NewCertificates0033.obstruction1061
  · exact NewCertificates0033.obstruction1062
  · exact NewCertificates0033.obstruction1063
end Nut8.FiniteSupport022
