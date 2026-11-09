import SupportData150
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport150
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0219.C7028, NewCertificates0219.C7029, NewCertificates0219.C7030, NewCertificates0219.C7031, NewCertificates0219.C7032, NewCertificates0219.C7033, NewCertificates0219.C7034, NewCertificates0219.C7035} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0219.C7036, NewCertificates0219.C7037, NewCertificates0219.C7038, NewCertificates0219.C7039, NewCertificates0220.C7040, NewCertificates0220.C7041, NewCertificates0220.C7042, NewCertificates0220.C7043} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0220.C7044, NewCertificates0220.C7045, NewCertificates0220.C7046, NewCertificates0220.C7047, NewCertificates0220.C7048, NewCertificates0220.C7049, NewCertificates0220.C7050, NewCertificates0220.C7051} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0220.C7052, NewCertificates0220.C7053, NewCertificates0220.C7054, NewCertificates0220.C7055, NewCertificates0220.C7056, NewCertificates0220.C7057, NewCertificates0220.C7058, NewCertificates0220.C7059} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0219.obstruction7028
  · exact NewCertificates0219.obstruction7029
  · exact NewCertificates0219.obstruction7030
  · exact NewCertificates0219.obstruction7031
  · exact NewCertificates0219.obstruction7032
  · exact NewCertificates0219.obstruction7033
  · exact NewCertificates0219.obstruction7034
  · exact NewCertificates0219.obstruction7035
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0219.obstruction7036
  · exact NewCertificates0219.obstruction7037
  · exact NewCertificates0219.obstruction7038
  · exact NewCertificates0219.obstruction7039
  · exact NewCertificates0220.obstruction7040
  · exact NewCertificates0220.obstruction7041
  · exact NewCertificates0220.obstruction7042
  · exact NewCertificates0220.obstruction7043
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0220.obstruction7044
  · exact NewCertificates0220.obstruction7045
  · exact NewCertificates0220.obstruction7046
  · exact NewCertificates0220.obstruction7047
  · exact NewCertificates0220.obstruction7048
  · exact NewCertificates0220.obstruction7049
  · exact NewCertificates0220.obstruction7050
  · exact NewCertificates0220.obstruction7051
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0220.obstruction7052
  · exact NewCertificates0220.obstruction7053
  · exact NewCertificates0220.obstruction7054
  · exact NewCertificates0220.obstruction7055
  · exact NewCertificates0220.obstruction7056
  · exact NewCertificates0220.obstruction7057
  · exact NewCertificates0220.obstruction7058
  · exact NewCertificates0220.obstruction7059
end Nut8.FiniteSupport150
