import SupportData151
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport151
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0220.C7068, NewCertificates0220.C7069, NewCertificates0220.C7070, NewCertificates0220.C7071, NewCertificates0221.C7072, NewCertificates0221.C7073, NewCertificates0221.C7074, NewCertificates0221.C7075} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0221.C7076, NewCertificates0221.C7077, NewCertificates0221.C7078, NewCertificates0221.C7079, NewCertificates0221.C7080, NewCertificates0221.C7081, NewCertificates0221.C7082, NewCertificates0221.C7083} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0221.C7084, NewCertificates0221.C7085, NewCertificates0221.C7086, NewCertificates0221.C7087, NewCertificates0221.C7088, NewCertificates0221.C7089, NewCertificates0221.C7090, NewCertificates0221.C7091} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0221.C7092, NewCertificates0221.C7093, NewCertificates0221.C7094, NewCertificates0221.C7095, NewCertificates0221.C7096, NewCertificates0221.C7097, NewCertificates0221.C7098, NewCertificates0221.C7099} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0220.obstruction7068
  · exact NewCertificates0220.obstruction7069
  · exact NewCertificates0220.obstruction7070
  · exact NewCertificates0220.obstruction7071
  · exact NewCertificates0221.obstruction7072
  · exact NewCertificates0221.obstruction7073
  · exact NewCertificates0221.obstruction7074
  · exact NewCertificates0221.obstruction7075
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0221.obstruction7076
  · exact NewCertificates0221.obstruction7077
  · exact NewCertificates0221.obstruction7078
  · exact NewCertificates0221.obstruction7079
  · exact NewCertificates0221.obstruction7080
  · exact NewCertificates0221.obstruction7081
  · exact NewCertificates0221.obstruction7082
  · exact NewCertificates0221.obstruction7083
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0221.obstruction7084
  · exact NewCertificates0221.obstruction7085
  · exact NewCertificates0221.obstruction7086
  · exact NewCertificates0221.obstruction7087
  · exact NewCertificates0221.obstruction7088
  · exact NewCertificates0221.obstruction7089
  · exact NewCertificates0221.obstruction7090
  · exact NewCertificates0221.obstruction7091
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0221.obstruction7092
  · exact NewCertificates0221.obstruction7093
  · exact NewCertificates0221.obstruction7094
  · exact NewCertificates0221.obstruction7095
  · exact NewCertificates0221.obstruction7096
  · exact NewCertificates0221.obstruction7097
  · exact NewCertificates0221.obstruction7098
  · exact NewCertificates0221.obstruction7099
end Nut8.FiniteSupport151
