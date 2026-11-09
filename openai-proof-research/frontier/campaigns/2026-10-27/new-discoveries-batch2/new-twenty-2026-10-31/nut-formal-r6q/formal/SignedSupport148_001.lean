import SupportData148
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport148
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0215.C6900, NewCertificates0215.C6901, NewCertificates0215.C6902, NewCertificates0215.C6903, NewCertificates0215.C6904, NewCertificates0215.C6905, NewCertificates0215.C6906, NewCertificates0215.C6907} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0215.C6908, NewCertificates0215.C6909, NewCertificates0215.C6910, NewCertificates0215.C6911, NewCertificates0216.C6912, NewCertificates0216.C6913, NewCertificates0216.C6914, NewCertificates0216.C6915} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0216.C6916, NewCertificates0216.C6917, NewCertificates0216.C6918, NewCertificates0216.C6919} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0216.C6920, NewCertificates0216.C6921, NewCertificates0216.C6922, NewCertificates0216.C6923} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0215.obstruction6900
  · exact NewCertificates0215.obstruction6901
  · exact NewCertificates0215.obstruction6902
  · exact NewCertificates0215.obstruction6903
  · exact NewCertificates0215.obstruction6904
  · exact NewCertificates0215.obstruction6905
  · exact NewCertificates0215.obstruction6906
  · exact NewCertificates0215.obstruction6907
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0215.obstruction6908
  · exact NewCertificates0215.obstruction6909
  · exact NewCertificates0215.obstruction6910
  · exact NewCertificates0215.obstruction6911
  · exact NewCertificates0216.obstruction6912
  · exact NewCertificates0216.obstruction6913
  · exact NewCertificates0216.obstruction6914
  · exact NewCertificates0216.obstruction6915
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0216.obstruction6916
  · exact NewCertificates0216.obstruction6917
  · exact NewCertificates0216.obstruction6918
  · exact NewCertificates0216.obstruction6919
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0216.obstruction6920
  · exact NewCertificates0216.obstruction6921
  · exact NewCertificates0216.obstruction6922
  · exact NewCertificates0216.obstruction6923
end Nut8.FiniteSupport148
