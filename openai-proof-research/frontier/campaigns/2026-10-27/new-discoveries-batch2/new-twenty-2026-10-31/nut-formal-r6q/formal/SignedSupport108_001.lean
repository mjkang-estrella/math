import SupportData108
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport108
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0158.C5062, NewCertificates0158.C5063, NewCertificates0158.C5064, NewCertificates0158.C5065, NewCertificates0158.C5066, NewCertificates0158.C5067, NewCertificates0158.C5068, NewCertificates0158.C5069} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0158.C5070, NewCertificates0158.C5071, NewCertificates0158.C5072, NewCertificates0158.C5073, NewCertificates0158.C5074, NewCertificates0158.C5075, NewCertificates0158.C5076, NewCertificates0158.C5077} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0158.C5078, NewCertificates0158.C5079, NewCertificates0158.C5080, NewCertificates0158.C5081, NewCertificates0158.C5082, NewCertificates0158.C5083, NewCertificates0158.C5084, NewCertificates0158.C5085} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0158.C5086, NewCertificates0158.C5087, NewCertificates0159.C5088, NewCertificates0159.C5089, NewCertificates0159.C5090, NewCertificates0159.C5091, NewCertificates0159.C5092, NewCertificates0159.C5093} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0158.obstruction5062
  · exact NewCertificates0158.obstruction5063
  · exact NewCertificates0158.obstruction5064
  · exact NewCertificates0158.obstruction5065
  · exact NewCertificates0158.obstruction5066
  · exact NewCertificates0158.obstruction5067
  · exact NewCertificates0158.obstruction5068
  · exact NewCertificates0158.obstruction5069
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0158.obstruction5070
  · exact NewCertificates0158.obstruction5071
  · exact NewCertificates0158.obstruction5072
  · exact NewCertificates0158.obstruction5073
  · exact NewCertificates0158.obstruction5074
  · exact NewCertificates0158.obstruction5075
  · exact NewCertificates0158.obstruction5076
  · exact NewCertificates0158.obstruction5077
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0158.obstruction5078
  · exact NewCertificates0158.obstruction5079
  · exact NewCertificates0158.obstruction5080
  · exact NewCertificates0158.obstruction5081
  · exact NewCertificates0158.obstruction5082
  · exact NewCertificates0158.obstruction5083
  · exact NewCertificates0158.obstruction5084
  · exact NewCertificates0158.obstruction5085
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0158.obstruction5086
  · exact NewCertificates0158.obstruction5087
  · exact NewCertificates0159.obstruction5088
  · exact NewCertificates0159.obstruction5089
  · exact NewCertificates0159.obstruction5090
  · exact NewCertificates0159.obstruction5091
  · exact NewCertificates0159.obstruction5092
  · exact NewCertificates0159.obstruction5093
end Nut8.FiniteSupport108
