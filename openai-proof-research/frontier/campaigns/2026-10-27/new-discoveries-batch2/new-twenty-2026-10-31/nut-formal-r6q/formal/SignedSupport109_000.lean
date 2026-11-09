import SupportData109
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport109
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0160.C5126, NewCertificates0160.C5127, NewCertificates0160.C5128, NewCertificates0160.C5129, NewCertificates0160.C5130, NewCertificates0160.C5131, NewCertificates0160.C5132, NewCertificates0160.C5133, NewCertificates0160.C5134, NewCertificates0160.C5135, NewCertificates0160.C5136, NewCertificates0160.C5137, NewCertificates0160.C5138, NewCertificates0160.C5139, NewCertificates0160.C5140, NewCertificates0160.C5141} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0160.C5142, NewCertificates0160.C5143, NewCertificates0160.C5144, NewCertificates0160.C5145, NewCertificates0160.C5146, NewCertificates0160.C5147, NewCertificates0160.C5148, NewCertificates0160.C5149} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0160.C5150, NewCertificates0160.C5151, NewCertificates0161.C5152, NewCertificates0161.C5153, NewCertificates0161.C5154, NewCertificates0161.C5155, NewCertificates0161.C5156, NewCertificates0161.C5157} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0161.C5158, NewCertificates0161.C5159, NewCertificates0161.C5160, NewCertificates0161.C5161} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0160.obstruction5126
  · exact NewCertificates0160.obstruction5127
  · exact NewCertificates0160.obstruction5128
  · exact NewCertificates0160.obstruction5129
  · exact NewCertificates0160.obstruction5130
  · exact NewCertificates0160.obstruction5131
  · exact NewCertificates0160.obstruction5132
  · exact NewCertificates0160.obstruction5133
  · exact NewCertificates0160.obstruction5134
  · exact NewCertificates0160.obstruction5135
  · exact NewCertificates0160.obstruction5136
  · exact NewCertificates0160.obstruction5137
  · exact NewCertificates0160.obstruction5138
  · exact NewCertificates0160.obstruction5139
  · exact NewCertificates0160.obstruction5140
  · exact NewCertificates0160.obstruction5141
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0160.obstruction5142
  · exact NewCertificates0160.obstruction5143
  · exact NewCertificates0160.obstruction5144
  · exact NewCertificates0160.obstruction5145
  · exact NewCertificates0160.obstruction5146
  · exact NewCertificates0160.obstruction5147
  · exact NewCertificates0160.obstruction5148
  · exact NewCertificates0160.obstruction5149
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0160.obstruction5150
  · exact NewCertificates0160.obstruction5151
  · exact NewCertificates0161.obstruction5152
  · exact NewCertificates0161.obstruction5153
  · exact NewCertificates0161.obstruction5154
  · exact NewCertificates0161.obstruction5155
  · exact NewCertificates0161.obstruction5156
  · exact NewCertificates0161.obstruction5157
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0161.obstruction5158
  · exact NewCertificates0161.obstruction5159
  · exact NewCertificates0161.obstruction5160
  · exact NewCertificates0161.obstruction5161
end Nut8.FiniteSupport109
