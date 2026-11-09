import SupportData128
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport128
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0191.C6132, NewCertificates0191.C6133, NewCertificates0191.C6134, NewCertificates0191.C6135, NewCertificates0191.C6136, NewCertificates0191.C6137, NewCertificates0191.C6138, NewCertificates0191.C6139, NewCertificates0191.C6140, NewCertificates0191.C6141, NewCertificates0191.C6142, NewCertificates0191.C6143, NewCertificates0192.C6144, NewCertificates0192.C6145, NewCertificates0192.C6146, NewCertificates0192.C6147} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0192.C6148, NewCertificates0192.C6149, NewCertificates0192.C6150, NewCertificates0192.C6151, NewCertificates0192.C6152, NewCertificates0192.C6153, NewCertificates0192.C6154, NewCertificates0192.C6155, NewCertificates0192.C6156, NewCertificates0192.C6157, NewCertificates0192.C6158, NewCertificates0192.C6159, NewCertificates0192.C6160, NewCertificates0192.C6161, NewCertificates0192.C6162, NewCertificates0192.C6163} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0191.obstruction6132
  · exact NewCertificates0191.obstruction6133
  · exact NewCertificates0191.obstruction6134
  · exact NewCertificates0191.obstruction6135
  · exact NewCertificates0191.obstruction6136
  · exact NewCertificates0191.obstruction6137
  · exact NewCertificates0191.obstruction6138
  · exact NewCertificates0191.obstruction6139
  · exact NewCertificates0191.obstruction6140
  · exact NewCertificates0191.obstruction6141
  · exact NewCertificates0191.obstruction6142
  · exact NewCertificates0191.obstruction6143
  · exact NewCertificates0192.obstruction6144
  · exact NewCertificates0192.obstruction6145
  · exact NewCertificates0192.obstruction6146
  · exact NewCertificates0192.obstruction6147
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0192.obstruction6148
  · exact NewCertificates0192.obstruction6149
  · exact NewCertificates0192.obstruction6150
  · exact NewCertificates0192.obstruction6151
  · exact NewCertificates0192.obstruction6152
  · exact NewCertificates0192.obstruction6153
  · exact NewCertificates0192.obstruction6154
  · exact NewCertificates0192.obstruction6155
  · exact NewCertificates0192.obstruction6156
  · exact NewCertificates0192.obstruction6157
  · exact NewCertificates0192.obstruction6158
  · exact NewCertificates0192.obstruction6159
  · exact NewCertificates0192.obstruction6160
  · exact NewCertificates0192.obstruction6161
  · exact NewCertificates0192.obstruction6162
  · exact NewCertificates0192.obstruction6163
end Nut8.FiniteSupport128
