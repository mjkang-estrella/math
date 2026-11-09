import SupportData123
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport123
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0187.C6004, NewCertificates0187.C6005, NewCertificates0187.C6006, NewCertificates0187.C6007, NewCertificates0187.C6008, NewCertificates0187.C6009, NewCertificates0187.C6010, NewCertificates0187.C6011} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0187.C6012, NewCertificates0187.C6013, NewCertificates0187.C6014, NewCertificates0187.C6015, NewCertificates0188.C6016, NewCertificates0188.C6017, NewCertificates0188.C6018, NewCertificates0188.C6019} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0188.C6020, NewCertificates0188.C6021, NewCertificates0188.C6022, NewCertificates0188.C6023, NewCertificates0188.C6024, NewCertificates0188.C6025, NewCertificates0188.C6026, NewCertificates0188.C6027} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0188.C6028, NewCertificates0188.C6029, NewCertificates0188.C6030, NewCertificates0188.C6031, NewCertificates0188.C6032, NewCertificates0188.C6033, NewCertificates0188.C6034, NewCertificates0188.C6035} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0187.obstruction6004
  · exact NewCertificates0187.obstruction6005
  · exact NewCertificates0187.obstruction6006
  · exact NewCertificates0187.obstruction6007
  · exact NewCertificates0187.obstruction6008
  · exact NewCertificates0187.obstruction6009
  · exact NewCertificates0187.obstruction6010
  · exact NewCertificates0187.obstruction6011
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0187.obstruction6012
  · exact NewCertificates0187.obstruction6013
  · exact NewCertificates0187.obstruction6014
  · exact NewCertificates0187.obstruction6015
  · exact NewCertificates0188.obstruction6016
  · exact NewCertificates0188.obstruction6017
  · exact NewCertificates0188.obstruction6018
  · exact NewCertificates0188.obstruction6019
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0188.obstruction6020
  · exact NewCertificates0188.obstruction6021
  · exact NewCertificates0188.obstruction6022
  · exact NewCertificates0188.obstruction6023
  · exact NewCertificates0188.obstruction6024
  · exact NewCertificates0188.obstruction6025
  · exact NewCertificates0188.obstruction6026
  · exact NewCertificates0188.obstruction6027
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0188.obstruction6028
  · exact NewCertificates0188.obstruction6029
  · exact NewCertificates0188.obstruction6030
  · exact NewCertificates0188.obstruction6031
  · exact NewCertificates0188.obstruction6032
  · exact NewCertificates0188.obstruction6033
  · exact NewCertificates0188.obstruction6034
  · exact NewCertificates0188.obstruction6035
end Nut8.FiniteSupport123
