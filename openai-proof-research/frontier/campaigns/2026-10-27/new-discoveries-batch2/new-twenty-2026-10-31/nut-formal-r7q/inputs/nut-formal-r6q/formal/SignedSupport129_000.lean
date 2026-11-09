import SupportData129
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport129
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0192.C6164, NewCertificates0192.C6165, NewCertificates0192.C6166, NewCertificates0192.C6167, NewCertificates0192.C6168, NewCertificates0192.C6169, NewCertificates0192.C6170, NewCertificates0192.C6171, NewCertificates0192.C6172, NewCertificates0192.C6173, NewCertificates0192.C6174, NewCertificates0192.C6175, NewCertificates0193.C6176, NewCertificates0193.C6177, NewCertificates0193.C6178, NewCertificates0193.C6179} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0193.C6180, NewCertificates0193.C6181, NewCertificates0193.C6182, NewCertificates0193.C6183, NewCertificates0193.C6184, NewCertificates0193.C6185, NewCertificates0193.C6186, NewCertificates0193.C6187, NewCertificates0193.C6188, NewCertificates0193.C6189, NewCertificates0193.C6190, NewCertificates0193.C6191, NewCertificates0193.C6192, NewCertificates0193.C6193, NewCertificates0193.C6194, NewCertificates0193.C6195} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0192.obstruction6164
  · exact NewCertificates0192.obstruction6165
  · exact NewCertificates0192.obstruction6166
  · exact NewCertificates0192.obstruction6167
  · exact NewCertificates0192.obstruction6168
  · exact NewCertificates0192.obstruction6169
  · exact NewCertificates0192.obstruction6170
  · exact NewCertificates0192.obstruction6171
  · exact NewCertificates0192.obstruction6172
  · exact NewCertificates0192.obstruction6173
  · exact NewCertificates0192.obstruction6174
  · exact NewCertificates0192.obstruction6175
  · exact NewCertificates0193.obstruction6176
  · exact NewCertificates0193.obstruction6177
  · exact NewCertificates0193.obstruction6178
  · exact NewCertificates0193.obstruction6179
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0193.obstruction6180
  · exact NewCertificates0193.obstruction6181
  · exact NewCertificates0193.obstruction6182
  · exact NewCertificates0193.obstruction6183
  · exact NewCertificates0193.obstruction6184
  · exact NewCertificates0193.obstruction6185
  · exact NewCertificates0193.obstruction6186
  · exact NewCertificates0193.obstruction6187
  · exact NewCertificates0193.obstruction6188
  · exact NewCertificates0193.obstruction6189
  · exact NewCertificates0193.obstruction6190
  · exact NewCertificates0193.obstruction6191
  · exact NewCertificates0193.obstruction6192
  · exact NewCertificates0193.obstruction6193
  · exact NewCertificates0193.obstruction6194
  · exact NewCertificates0193.obstruction6195
end Nut8.FiniteSupport129
