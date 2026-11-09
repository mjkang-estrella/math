import SupportData192
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport192
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0283.C9076, NewCertificates0283.C9077, NewCertificates0283.C9078, NewCertificates0283.C9079, NewCertificates0283.C9080, NewCertificates0283.C9081, NewCertificates0283.C9082, NewCertificates0283.C9083, NewCertificates0283.C9084, NewCertificates0283.C9085, NewCertificates0283.C9086, NewCertificates0283.C9087, NewCertificates0284.C9088, NewCertificates0284.C9089, NewCertificates0284.C9090, NewCertificates0284.C9091, NewCertificates0284.C9092, NewCertificates0284.C9093, NewCertificates0284.C9094, NewCertificates0284.C9095, NewCertificates0284.C9096, NewCertificates0284.C9097, NewCertificates0284.C9098, NewCertificates0284.C9099, NewCertificates0284.C9100, NewCertificates0284.C9101, NewCertificates0284.C9102, NewCertificates0284.C9103, NewCertificates0284.C9104, NewCertificates0284.C9105, NewCertificates0284.C9106, NewCertificates0284.C9107} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0284.C9108, NewCertificates0284.C9109, NewCertificates0284.C9110, NewCertificates0284.C9111, NewCertificates0284.C9112, NewCertificates0284.C9113, NewCertificates0284.C9114, NewCertificates0284.C9115, NewCertificates0284.C9116, NewCertificates0284.C9117, NewCertificates0284.C9118, NewCertificates0284.C9119, NewCertificates0285.C9120, NewCertificates0285.C9121, NewCertificates0285.C9122, NewCertificates0285.C9123} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0283.obstruction9076
  · exact NewCertificates0283.obstruction9077
  · exact NewCertificates0283.obstruction9078
  · exact NewCertificates0283.obstruction9079
  · exact NewCertificates0283.obstruction9080
  · exact NewCertificates0283.obstruction9081
  · exact NewCertificates0283.obstruction9082
  · exact NewCertificates0283.obstruction9083
  · exact NewCertificates0283.obstruction9084
  · exact NewCertificates0283.obstruction9085
  · exact NewCertificates0283.obstruction9086
  · exact NewCertificates0283.obstruction9087
  · exact NewCertificates0284.obstruction9088
  · exact NewCertificates0284.obstruction9089
  · exact NewCertificates0284.obstruction9090
  · exact NewCertificates0284.obstruction9091
  · exact NewCertificates0284.obstruction9092
  · exact NewCertificates0284.obstruction9093
  · exact NewCertificates0284.obstruction9094
  · exact NewCertificates0284.obstruction9095
  · exact NewCertificates0284.obstruction9096
  · exact NewCertificates0284.obstruction9097
  · exact NewCertificates0284.obstruction9098
  · exact NewCertificates0284.obstruction9099
  · exact NewCertificates0284.obstruction9100
  · exact NewCertificates0284.obstruction9101
  · exact NewCertificates0284.obstruction9102
  · exact NewCertificates0284.obstruction9103
  · exact NewCertificates0284.obstruction9104
  · exact NewCertificates0284.obstruction9105
  · exact NewCertificates0284.obstruction9106
  · exact NewCertificates0284.obstruction9107
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0284.obstruction9108
  · exact NewCertificates0284.obstruction9109
  · exact NewCertificates0284.obstruction9110
  · exact NewCertificates0284.obstruction9111
  · exact NewCertificates0284.obstruction9112
  · exact NewCertificates0284.obstruction9113
  · exact NewCertificates0284.obstruction9114
  · exact NewCertificates0284.obstruction9115
  · exact NewCertificates0284.obstruction9116
  · exact NewCertificates0284.obstruction9117
  · exact NewCertificates0284.obstruction9118
  · exact NewCertificates0284.obstruction9119
  · exact NewCertificates0285.obstruction9120
  · exact NewCertificates0285.obstruction9121
  · exact NewCertificates0285.obstruction9122
  · exact NewCertificates0285.obstruction9123
end Nut8.FiniteSupport192
