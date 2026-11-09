import SupportData127
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport127
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0190.C6100, NewCertificates0190.C6101, NewCertificates0190.C6102, NewCertificates0190.C6103, NewCertificates0190.C6104, NewCertificates0190.C6105, NewCertificates0190.C6106, NewCertificates0190.C6107, NewCertificates0190.C6108, NewCertificates0190.C6109, NewCertificates0190.C6110, NewCertificates0190.C6111, NewCertificates0191.C6112, NewCertificates0191.C6113, NewCertificates0191.C6114, NewCertificates0191.C6115, NewCertificates0191.C6116, NewCertificates0191.C6117, NewCertificates0191.C6118, NewCertificates0191.C6119, NewCertificates0191.C6120, NewCertificates0191.C6121, NewCertificates0191.C6122, NewCertificates0191.C6123, NewCertificates0191.C6124, NewCertificates0191.C6125, NewCertificates0191.C6126, NewCertificates0191.C6127, NewCertificates0191.C6128, NewCertificates0191.C6129, NewCertificates0191.C6130, NewCertificates0191.C6131} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0190.obstruction6100
  · exact NewCertificates0190.obstruction6101
  · exact NewCertificates0190.obstruction6102
  · exact NewCertificates0190.obstruction6103
  · exact NewCertificates0190.obstruction6104
  · exact NewCertificates0190.obstruction6105
  · exact NewCertificates0190.obstruction6106
  · exact NewCertificates0190.obstruction6107
  · exact NewCertificates0190.obstruction6108
  · exact NewCertificates0190.obstruction6109
  · exact NewCertificates0190.obstruction6110
  · exact NewCertificates0190.obstruction6111
  · exact NewCertificates0191.obstruction6112
  · exact NewCertificates0191.obstruction6113
  · exact NewCertificates0191.obstruction6114
  · exact NewCertificates0191.obstruction6115
  · exact NewCertificates0191.obstruction6116
  · exact NewCertificates0191.obstruction6117
  · exact NewCertificates0191.obstruction6118
  · exact NewCertificates0191.obstruction6119
  · exact NewCertificates0191.obstruction6120
  · exact NewCertificates0191.obstruction6121
  · exact NewCertificates0191.obstruction6122
  · exact NewCertificates0191.obstruction6123
  · exact NewCertificates0191.obstruction6124
  · exact NewCertificates0191.obstruction6125
  · exact NewCertificates0191.obstruction6126
  · exact NewCertificates0191.obstruction6127
  · exact NewCertificates0191.obstruction6128
  · exact NewCertificates0191.obstruction6129
  · exact NewCertificates0191.obstruction6130
  · exact NewCertificates0191.obstruction6131
end Nut8.FiniteSupport127
