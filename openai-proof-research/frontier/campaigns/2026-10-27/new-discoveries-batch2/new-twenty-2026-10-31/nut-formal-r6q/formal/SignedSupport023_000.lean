import SupportData023
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport023
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0033.C1064, NewCertificates0033.C1065, NewCertificates0033.C1066, NewCertificates0033.C1067, NewCertificates0033.C1068, NewCertificates0033.C1069, NewCertificates0033.C1070, NewCertificates0033.C1071, NewCertificates0033.C1072, NewCertificates0033.C1073, NewCertificates0033.C1074, NewCertificates0033.C1075, NewCertificates0033.C1076, NewCertificates0033.C1077, NewCertificates0033.C1078, NewCertificates0033.C1079} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0033.C1080, NewCertificates0033.C1081, NewCertificates0033.C1082, NewCertificates0033.C1083, NewCertificates0033.C1084, NewCertificates0033.C1085, NewCertificates0033.C1086, NewCertificates0033.C1087} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0034.C1088, NewCertificates0034.C1089, NewCertificates0034.C1090, NewCertificates0034.C1091, NewCertificates0034.C1092, NewCertificates0034.C1093, NewCertificates0034.C1094, NewCertificates0034.C1095} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0034.C1096, NewCertificates0034.C1097, NewCertificates0034.C1098, NewCertificates0034.C1099} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0033.obstruction1064
  · exact NewCertificates0033.obstruction1065
  · exact NewCertificates0033.obstruction1066
  · exact NewCertificates0033.obstruction1067
  · exact NewCertificates0033.obstruction1068
  · exact NewCertificates0033.obstruction1069
  · exact NewCertificates0033.obstruction1070
  · exact NewCertificates0033.obstruction1071
  · exact NewCertificates0033.obstruction1072
  · exact NewCertificates0033.obstruction1073
  · exact NewCertificates0033.obstruction1074
  · exact NewCertificates0033.obstruction1075
  · exact NewCertificates0033.obstruction1076
  · exact NewCertificates0033.obstruction1077
  · exact NewCertificates0033.obstruction1078
  · exact NewCertificates0033.obstruction1079
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0033.obstruction1080
  · exact NewCertificates0033.obstruction1081
  · exact NewCertificates0033.obstruction1082
  · exact NewCertificates0033.obstruction1083
  · exact NewCertificates0033.obstruction1084
  · exact NewCertificates0033.obstruction1085
  · exact NewCertificates0033.obstruction1086
  · exact NewCertificates0033.obstruction1087
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0034.obstruction1088
  · exact NewCertificates0034.obstruction1089
  · exact NewCertificates0034.obstruction1090
  · exact NewCertificates0034.obstruction1091
  · exact NewCertificates0034.obstruction1092
  · exact NewCertificates0034.obstruction1093
  · exact NewCertificates0034.obstruction1094
  · exact NewCertificates0034.obstruction1095
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0034.obstruction1096
  · exact NewCertificates0034.obstruction1097
  · exact NewCertificates0034.obstruction1098
  · exact NewCertificates0034.obstruction1099
end Nut8.FiniteSupport023
