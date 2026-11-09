import SupportData021
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport021
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0030.C984, NewCertificates0030.C985, NewCertificates0030.C986, NewCertificates0030.C987, NewCertificates0030.C988, NewCertificates0030.C989, NewCertificates0030.C990, NewCertificates0030.C991, NewCertificates0031.C992, NewCertificates0031.C993, NewCertificates0031.C994, NewCertificates0031.C995, NewCertificates0031.C996, NewCertificates0031.C997, NewCertificates0031.C998, NewCertificates0031.C999} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0031.C1000, NewCertificates0031.C1001, NewCertificates0031.C1002, NewCertificates0031.C1003, NewCertificates0031.C1004, NewCertificates0031.C1005, NewCertificates0031.C1006, NewCertificates0031.C1007, NewCertificates0031.C1008, NewCertificates0031.C1009, NewCertificates0031.C1010, NewCertificates0031.C1011, NewCertificates0031.C1012, NewCertificates0031.C1013, NewCertificates0031.C1014, NewCertificates0031.C1015} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0031.C1016, NewCertificates0031.C1017, NewCertificates0031.C1018, NewCertificates0031.C1019, NewCertificates0031.C1020, NewCertificates0031.C1021, NewCertificates0031.C1022, NewCertificates0031.C1023, NewCertificates0032.C1024, NewCertificates0032.C1025, NewCertificates0032.C1026, NewCertificates0032.C1027, NewCertificates0032.C1028, NewCertificates0032.C1029, NewCertificates0032.C1030, NewCertificates0032.C1031} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0030.obstruction984
  · exact NewCertificates0030.obstruction985
  · exact NewCertificates0030.obstruction986
  · exact NewCertificates0030.obstruction987
  · exact NewCertificates0030.obstruction988
  · exact NewCertificates0030.obstruction989
  · exact NewCertificates0030.obstruction990
  · exact NewCertificates0030.obstruction991
  · exact NewCertificates0031.obstruction992
  · exact NewCertificates0031.obstruction993
  · exact NewCertificates0031.obstruction994
  · exact NewCertificates0031.obstruction995
  · exact NewCertificates0031.obstruction996
  · exact NewCertificates0031.obstruction997
  · exact NewCertificates0031.obstruction998
  · exact NewCertificates0031.obstruction999
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0031.obstruction1000
  · exact NewCertificates0031.obstruction1001
  · exact NewCertificates0031.obstruction1002
  · exact NewCertificates0031.obstruction1003
  · exact NewCertificates0031.obstruction1004
  · exact NewCertificates0031.obstruction1005
  · exact NewCertificates0031.obstruction1006
  · exact NewCertificates0031.obstruction1007
  · exact NewCertificates0031.obstruction1008
  · exact NewCertificates0031.obstruction1009
  · exact NewCertificates0031.obstruction1010
  · exact NewCertificates0031.obstruction1011
  · exact NewCertificates0031.obstruction1012
  · exact NewCertificates0031.obstruction1013
  · exact NewCertificates0031.obstruction1014
  · exact NewCertificates0031.obstruction1015
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0031.obstruction1016
  · exact NewCertificates0031.obstruction1017
  · exact NewCertificates0031.obstruction1018
  · exact NewCertificates0031.obstruction1019
  · exact NewCertificates0031.obstruction1020
  · exact NewCertificates0031.obstruction1021
  · exact NewCertificates0031.obstruction1022
  · exact NewCertificates0031.obstruction1023
  · exact NewCertificates0032.obstruction1024
  · exact NewCertificates0032.obstruction1025
  · exact NewCertificates0032.obstruction1026
  · exact NewCertificates0032.obstruction1027
  · exact NewCertificates0032.obstruction1028
  · exact NewCertificates0032.obstruction1029
  · exact NewCertificates0032.obstruction1030
  · exact NewCertificates0032.obstruction1031
end Nut8.FiniteSupport021
