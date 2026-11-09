import SupportData173
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport173
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0250.C8004, NewCertificates0250.C8005, NewCertificates0250.C8006, NewCertificates0250.C8007, NewCertificates0250.C8008, NewCertificates0250.C8009, NewCertificates0250.C8010, NewCertificates0250.C8011, NewCertificates0250.C8012, NewCertificates0250.C8013, NewCertificates0250.C8014, NewCertificates0250.C8015, NewCertificates0250.C8016, NewCertificates0250.C8017, NewCertificates0250.C8018, NewCertificates0250.C8019} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0250.C8020, NewCertificates0250.C8021, NewCertificates0250.C8022, NewCertificates0250.C8023, NewCertificates0250.C8024, NewCertificates0250.C8025, NewCertificates0250.C8026, NewCertificates0250.C8027, NewCertificates0250.C8028, NewCertificates0250.C8029, NewCertificates0250.C8030, NewCertificates0250.C8031, NewCertificates0251.C8032, NewCertificates0251.C8033, NewCertificates0251.C8034, NewCertificates0251.C8035} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0251.C8036, NewCertificates0251.C8037, NewCertificates0251.C8038, NewCertificates0251.C8039, NewCertificates0251.C8040, NewCertificates0251.C8041, NewCertificates0251.C8042, NewCertificates0251.C8043, NewCertificates0251.C8044, NewCertificates0251.C8045, NewCertificates0251.C8046, NewCertificates0251.C8047, NewCertificates0251.C8048, NewCertificates0251.C8049, NewCertificates0251.C8050, NewCertificates0251.C8051} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0251.C8052, NewCertificates0251.C8053, NewCertificates0251.C8054, NewCertificates0251.C8055, NewCertificates0251.C8056, NewCertificates0251.C8057, NewCertificates0251.C8058, NewCertificates0251.C8059} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0250.obstruction8004
  · exact NewCertificates0250.obstruction8005
  · exact NewCertificates0250.obstruction8006
  · exact NewCertificates0250.obstruction8007
  · exact NewCertificates0250.obstruction8008
  · exact NewCertificates0250.obstruction8009
  · exact NewCertificates0250.obstruction8010
  · exact NewCertificates0250.obstruction8011
  · exact NewCertificates0250.obstruction8012
  · exact NewCertificates0250.obstruction8013
  · exact NewCertificates0250.obstruction8014
  · exact NewCertificates0250.obstruction8015
  · exact NewCertificates0250.obstruction8016
  · exact NewCertificates0250.obstruction8017
  · exact NewCertificates0250.obstruction8018
  · exact NewCertificates0250.obstruction8019
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0250.obstruction8020
  · exact NewCertificates0250.obstruction8021
  · exact NewCertificates0250.obstruction8022
  · exact NewCertificates0250.obstruction8023
  · exact NewCertificates0250.obstruction8024
  · exact NewCertificates0250.obstruction8025
  · exact NewCertificates0250.obstruction8026
  · exact NewCertificates0250.obstruction8027
  · exact NewCertificates0250.obstruction8028
  · exact NewCertificates0250.obstruction8029
  · exact NewCertificates0250.obstruction8030
  · exact NewCertificates0250.obstruction8031
  · exact NewCertificates0251.obstruction8032
  · exact NewCertificates0251.obstruction8033
  · exact NewCertificates0251.obstruction8034
  · exact NewCertificates0251.obstruction8035
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0251.obstruction8036
  · exact NewCertificates0251.obstruction8037
  · exact NewCertificates0251.obstruction8038
  · exact NewCertificates0251.obstruction8039
  · exact NewCertificates0251.obstruction8040
  · exact NewCertificates0251.obstruction8041
  · exact NewCertificates0251.obstruction8042
  · exact NewCertificates0251.obstruction8043
  · exact NewCertificates0251.obstruction8044
  · exact NewCertificates0251.obstruction8045
  · exact NewCertificates0251.obstruction8046
  · exact NewCertificates0251.obstruction8047
  · exact NewCertificates0251.obstruction8048
  · exact NewCertificates0251.obstruction8049
  · exact NewCertificates0251.obstruction8050
  · exact NewCertificates0251.obstruction8051
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0251.obstruction8052
  · exact NewCertificates0251.obstruction8053
  · exact NewCertificates0251.obstruction8054
  · exact NewCertificates0251.obstruction8055
  · exact NewCertificates0251.obstruction8056
  · exact NewCertificates0251.obstruction8057
  · exact NewCertificates0251.obstruction8058
  · exact NewCertificates0251.obstruction8059
end Nut8.FiniteSupport173
