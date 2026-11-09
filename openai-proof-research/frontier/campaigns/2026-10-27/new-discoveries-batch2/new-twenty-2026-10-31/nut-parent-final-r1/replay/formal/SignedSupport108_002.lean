import SupportData108
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport108
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0159.C5094, NewCertificates0159.C5095, NewCertificates0159.C5096, NewCertificates0159.C5097, NewCertificates0159.C5098, NewCertificates0159.C5099, NewCertificates0159.C5100, NewCertificates0159.C5101} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0159.C5102, NewCertificates0159.C5103, NewCertificates0159.C5104, NewCertificates0159.C5105} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0159.C5106, NewCertificates0159.C5107, NewCertificates0159.C5108, NewCertificates0159.C5109} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0159.C5110, NewCertificates0159.C5111, NewCertificates0159.C5112, NewCertificates0159.C5113} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5094
  · exact NewCertificates0159.obstruction5095
  · exact NewCertificates0159.obstruction5096
  · exact NewCertificates0159.obstruction5097
  · exact NewCertificates0159.obstruction5098
  · exact NewCertificates0159.obstruction5099
  · exact NewCertificates0159.obstruction5100
  · exact NewCertificates0159.obstruction5101
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5102
  · exact NewCertificates0159.obstruction5103
  · exact NewCertificates0159.obstruction5104
  · exact NewCertificates0159.obstruction5105
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5106
  · exact NewCertificates0159.obstruction5107
  · exact NewCertificates0159.obstruction5108
  · exact NewCertificates0159.obstruction5109
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5110
  · exact NewCertificates0159.obstruction5111
  · exact NewCertificates0159.obstruction5112
  · exact NewCertificates0159.obstruction5113
end Nut8.FiniteSupport108
