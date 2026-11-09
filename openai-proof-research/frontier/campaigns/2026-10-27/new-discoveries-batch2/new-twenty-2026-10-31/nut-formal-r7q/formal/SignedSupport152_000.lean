import SupportData152
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport152
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0223.C7140, NewCertificates0223.C7141, NewCertificates0223.C7142, NewCertificates0223.C7143, NewCertificates0223.C7144, NewCertificates0223.C7145, NewCertificates0223.C7146, NewCertificates0223.C7147} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0223.C7148, NewCertificates0223.C7149, NewCertificates0223.C7150, NewCertificates0223.C7151, NewCertificates0223.C7152, NewCertificates0223.C7153, NewCertificates0223.C7154, NewCertificates0223.C7155} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0223.C7156, NewCertificates0223.C7157, NewCertificates0223.C7158, NewCertificates0223.C7159, NewCertificates0223.C7160, NewCertificates0223.C7161, NewCertificates0223.C7162, NewCertificates0223.C7163} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0223.C7164, NewCertificates0223.C7165, NewCertificates0223.C7166, NewCertificates0223.C7167, NewCertificates0224.C7168, NewCertificates0224.C7169, NewCertificates0224.C7170, NewCertificates0224.C7171} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0223.obstruction7140
  · exact NewCertificates0223.obstruction7141
  · exact NewCertificates0223.obstruction7142
  · exact NewCertificates0223.obstruction7143
  · exact NewCertificates0223.obstruction7144
  · exact NewCertificates0223.obstruction7145
  · exact NewCertificates0223.obstruction7146
  · exact NewCertificates0223.obstruction7147
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0223.obstruction7148
  · exact NewCertificates0223.obstruction7149
  · exact NewCertificates0223.obstruction7150
  · exact NewCertificates0223.obstruction7151
  · exact NewCertificates0223.obstruction7152
  · exact NewCertificates0223.obstruction7153
  · exact NewCertificates0223.obstruction7154
  · exact NewCertificates0223.obstruction7155
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0223.obstruction7156
  · exact NewCertificates0223.obstruction7157
  · exact NewCertificates0223.obstruction7158
  · exact NewCertificates0223.obstruction7159
  · exact NewCertificates0223.obstruction7160
  · exact NewCertificates0223.obstruction7161
  · exact NewCertificates0223.obstruction7162
  · exact NewCertificates0223.obstruction7163
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0223.obstruction7164
  · exact NewCertificates0223.obstruction7165
  · exact NewCertificates0223.obstruction7166
  · exact NewCertificates0223.obstruction7167
  · exact NewCertificates0224.obstruction7168
  · exact NewCertificates0224.obstruction7169
  · exact NewCertificates0224.obstruction7170
  · exact NewCertificates0224.obstruction7171
end Nut8.FiniteSupport152
