import SupportData174
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport174
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0252.C8068, NewCertificates0252.C8069, NewCertificates0252.C8070, NewCertificates0252.C8071, NewCertificates0252.C8072, NewCertificates0252.C8073, NewCertificates0252.C8074, NewCertificates0252.C8075, NewCertificates0252.C8076, NewCertificates0252.C8077, NewCertificates0252.C8078, NewCertificates0252.C8079, NewCertificates0252.C8080, NewCertificates0252.C8081, NewCertificates0252.C8082, NewCertificates0252.C8083} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0252.C8084, NewCertificates0252.C8085, NewCertificates0252.C8086, NewCertificates0252.C8087, NewCertificates0252.C8088, NewCertificates0252.C8089, NewCertificates0252.C8090, NewCertificates0252.C8091, NewCertificates0252.C8092, NewCertificates0252.C8093, NewCertificates0252.C8094, NewCertificates0252.C8095, NewCertificates0253.C8096, NewCertificates0253.C8097, NewCertificates0253.C8098, NewCertificates0253.C8099} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0253.C8100, NewCertificates0253.C8101, NewCertificates0253.C8102, NewCertificates0253.C8103, NewCertificates0253.C8104, NewCertificates0253.C8105, NewCertificates0253.C8106, NewCertificates0253.C8107} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0253.C8108, NewCertificates0253.C8109, NewCertificates0253.C8110, NewCertificates0253.C8111, NewCertificates0253.C8112, NewCertificates0253.C8113, NewCertificates0253.C8114, NewCertificates0253.C8115} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0252.obstruction8068
  · exact NewCertificates0252.obstruction8069
  · exact NewCertificates0252.obstruction8070
  · exact NewCertificates0252.obstruction8071
  · exact NewCertificates0252.obstruction8072
  · exact NewCertificates0252.obstruction8073
  · exact NewCertificates0252.obstruction8074
  · exact NewCertificates0252.obstruction8075
  · exact NewCertificates0252.obstruction8076
  · exact NewCertificates0252.obstruction8077
  · exact NewCertificates0252.obstruction8078
  · exact NewCertificates0252.obstruction8079
  · exact NewCertificates0252.obstruction8080
  · exact NewCertificates0252.obstruction8081
  · exact NewCertificates0252.obstruction8082
  · exact NewCertificates0252.obstruction8083
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0252.obstruction8084
  · exact NewCertificates0252.obstruction8085
  · exact NewCertificates0252.obstruction8086
  · exact NewCertificates0252.obstruction8087
  · exact NewCertificates0252.obstruction8088
  · exact NewCertificates0252.obstruction8089
  · exact NewCertificates0252.obstruction8090
  · exact NewCertificates0252.obstruction8091
  · exact NewCertificates0252.obstruction8092
  · exact NewCertificates0252.obstruction8093
  · exact NewCertificates0252.obstruction8094
  · exact NewCertificates0252.obstruction8095
  · exact NewCertificates0253.obstruction8096
  · exact NewCertificates0253.obstruction8097
  · exact NewCertificates0253.obstruction8098
  · exact NewCertificates0253.obstruction8099
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0253.obstruction8100
  · exact NewCertificates0253.obstruction8101
  · exact NewCertificates0253.obstruction8102
  · exact NewCertificates0253.obstruction8103
  · exact NewCertificates0253.obstruction8104
  · exact NewCertificates0253.obstruction8105
  · exact NewCertificates0253.obstruction8106
  · exact NewCertificates0253.obstruction8107
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0253.obstruction8108
  · exact NewCertificates0253.obstruction8109
  · exact NewCertificates0253.obstruction8110
  · exact NewCertificates0253.obstruction8111
  · exact NewCertificates0253.obstruction8112
  · exact NewCertificates0253.obstruction8113
  · exact NewCertificates0253.obstruction8114
  · exact NewCertificates0253.obstruction8115
end Nut8.FiniteSupport174
