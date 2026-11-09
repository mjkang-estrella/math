import SupportData109
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport109
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0161.C5162, NewCertificates0161.C5163, NewCertificates0161.C5164, NewCertificates0161.C5165, NewCertificates0161.C5166, NewCertificates0161.C5167, NewCertificates0161.C5168, NewCertificates0161.C5169, NewCertificates0161.C5170, NewCertificates0161.C5171, NewCertificates0161.C5172, NewCertificates0161.C5173, NewCertificates0161.C5174, NewCertificates0161.C5175, NewCertificates0161.C5176, NewCertificates0161.C5177} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0161.C5178, NewCertificates0161.C5179, NewCertificates0161.C5180, NewCertificates0161.C5181, NewCertificates0161.C5182, NewCertificates0161.C5183, NewCertificates0162.C5184, NewCertificates0162.C5185} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0162.C5186, NewCertificates0162.C5187, NewCertificates0162.C5188, NewCertificates0162.C5189, NewCertificates0162.C5190, NewCertificates0162.C5191, NewCertificates0162.C5192, NewCertificates0162.C5193} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0162.C5194, NewCertificates0162.C5195, NewCertificates0162.C5196, NewCertificates0162.C5197} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0161.obstruction5162
  · exact NewCertificates0161.obstruction5163
  · exact NewCertificates0161.obstruction5164
  · exact NewCertificates0161.obstruction5165
  · exact NewCertificates0161.obstruction5166
  · exact NewCertificates0161.obstruction5167
  · exact NewCertificates0161.obstruction5168
  · exact NewCertificates0161.obstruction5169
  · exact NewCertificates0161.obstruction5170
  · exact NewCertificates0161.obstruction5171
  · exact NewCertificates0161.obstruction5172
  · exact NewCertificates0161.obstruction5173
  · exact NewCertificates0161.obstruction5174
  · exact NewCertificates0161.obstruction5175
  · exact NewCertificates0161.obstruction5176
  · exact NewCertificates0161.obstruction5177
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0161.obstruction5178
  · exact NewCertificates0161.obstruction5179
  · exact NewCertificates0161.obstruction5180
  · exact NewCertificates0161.obstruction5181
  · exact NewCertificates0161.obstruction5182
  · exact NewCertificates0161.obstruction5183
  · exact NewCertificates0162.obstruction5184
  · exact NewCertificates0162.obstruction5185
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0162.obstruction5186
  · exact NewCertificates0162.obstruction5187
  · exact NewCertificates0162.obstruction5188
  · exact NewCertificates0162.obstruction5189
  · exact NewCertificates0162.obstruction5190
  · exact NewCertificates0162.obstruction5191
  · exact NewCertificates0162.obstruction5192
  · exact NewCertificates0162.obstruction5193
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0162.obstruction5194
  · exact NewCertificates0162.obstruction5195
  · exact NewCertificates0162.obstruction5196
  · exact NewCertificates0162.obstruction5197
end Nut8.FiniteSupport109
