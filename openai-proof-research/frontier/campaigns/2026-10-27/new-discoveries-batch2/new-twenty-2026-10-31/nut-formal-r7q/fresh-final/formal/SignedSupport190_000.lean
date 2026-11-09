import SupportData190
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport190
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0280.C8980, NewCertificates0280.C8981, NewCertificates0280.C8982, NewCertificates0280.C8983, NewCertificates0280.C8984, NewCertificates0280.C8985, NewCertificates0280.C8986, NewCertificates0280.C8987, NewCertificates0280.C8988, NewCertificates0280.C8989, NewCertificates0280.C8990, NewCertificates0280.C8991, NewCertificates0281.C8992, NewCertificates0281.C8993, NewCertificates0281.C8994, NewCertificates0281.C8995, NewCertificates0281.C8996, NewCertificates0281.C8997, NewCertificates0281.C8998, NewCertificates0281.C8999, NewCertificates0281.C9000, NewCertificates0281.C9001, NewCertificates0281.C9002, NewCertificates0281.C9003, NewCertificates0281.C9004, NewCertificates0281.C9005, NewCertificates0281.C9006, NewCertificates0281.C9007, NewCertificates0281.C9008, NewCertificates0281.C9009, NewCertificates0281.C9010, NewCertificates0281.C9011} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0281.C9012, NewCertificates0281.C9013, NewCertificates0281.C9014, NewCertificates0281.C9015, NewCertificates0281.C9016, NewCertificates0281.C9017, NewCertificates0281.C9018, NewCertificates0281.C9019, NewCertificates0281.C9020, NewCertificates0281.C9021, NewCertificates0281.C9022, NewCertificates0281.C9023, NewCertificates0282.C9024, NewCertificates0282.C9025, NewCertificates0282.C9026, NewCertificates0282.C9027} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0280.obstruction8980
  · exact NewCertificates0280.obstruction8981
  · exact NewCertificates0280.obstruction8982
  · exact NewCertificates0280.obstruction8983
  · exact NewCertificates0280.obstruction8984
  · exact NewCertificates0280.obstruction8985
  · exact NewCertificates0280.obstruction8986
  · exact NewCertificates0280.obstruction8987
  · exact NewCertificates0280.obstruction8988
  · exact NewCertificates0280.obstruction8989
  · exact NewCertificates0280.obstruction8990
  · exact NewCertificates0280.obstruction8991
  · exact NewCertificates0281.obstruction8992
  · exact NewCertificates0281.obstruction8993
  · exact NewCertificates0281.obstruction8994
  · exact NewCertificates0281.obstruction8995
  · exact NewCertificates0281.obstruction8996
  · exact NewCertificates0281.obstruction8997
  · exact NewCertificates0281.obstruction8998
  · exact NewCertificates0281.obstruction8999
  · exact NewCertificates0281.obstruction9000
  · exact NewCertificates0281.obstruction9001
  · exact NewCertificates0281.obstruction9002
  · exact NewCertificates0281.obstruction9003
  · exact NewCertificates0281.obstruction9004
  · exact NewCertificates0281.obstruction9005
  · exact NewCertificates0281.obstruction9006
  · exact NewCertificates0281.obstruction9007
  · exact NewCertificates0281.obstruction9008
  · exact NewCertificates0281.obstruction9009
  · exact NewCertificates0281.obstruction9010
  · exact NewCertificates0281.obstruction9011
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0281.obstruction9012
  · exact NewCertificates0281.obstruction9013
  · exact NewCertificates0281.obstruction9014
  · exact NewCertificates0281.obstruction9015
  · exact NewCertificates0281.obstruction9016
  · exact NewCertificates0281.obstruction9017
  · exact NewCertificates0281.obstruction9018
  · exact NewCertificates0281.obstruction9019
  · exact NewCertificates0281.obstruction9020
  · exact NewCertificates0281.obstruction9021
  · exact NewCertificates0281.obstruction9022
  · exact NewCertificates0281.obstruction9023
  · exact NewCertificates0282.obstruction9024
  · exact NewCertificates0282.obstruction9025
  · exact NewCertificates0282.obstruction9026
  · exact NewCertificates0282.obstruction9027
end Nut8.FiniteSupport190
