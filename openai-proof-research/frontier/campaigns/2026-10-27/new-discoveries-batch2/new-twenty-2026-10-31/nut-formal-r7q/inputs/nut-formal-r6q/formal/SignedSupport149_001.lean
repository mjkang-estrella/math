import SupportData149
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport149
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0217.C6972, NewCertificates0217.C6973, NewCertificates0217.C6974, NewCertificates0217.C6975, NewCertificates0218.C6976, NewCertificates0218.C6977, NewCertificates0218.C6978, NewCertificates0218.C6979} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0218.C6980, NewCertificates0218.C6981, NewCertificates0218.C6982, NewCertificates0218.C6983} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0218.C6984, NewCertificates0218.C6985, NewCertificates0218.C6986, NewCertificates0218.C6987, NewCertificates0218.C6988, NewCertificates0218.C6989, NewCertificates0218.C6990, NewCertificates0218.C6991} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0218.C6992, NewCertificates0218.C6993, NewCertificates0218.C6994, NewCertificates0218.C6995} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0217.obstruction6972
  · exact NewCertificates0217.obstruction6973
  · exact NewCertificates0217.obstruction6974
  · exact NewCertificates0217.obstruction6975
  · exact NewCertificates0218.obstruction6976
  · exact NewCertificates0218.obstruction6977
  · exact NewCertificates0218.obstruction6978
  · exact NewCertificates0218.obstruction6979
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0218.obstruction6980
  · exact NewCertificates0218.obstruction6981
  · exact NewCertificates0218.obstruction6982
  · exact NewCertificates0218.obstruction6983
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0218.obstruction6984
  · exact NewCertificates0218.obstruction6985
  · exact NewCertificates0218.obstruction6986
  · exact NewCertificates0218.obstruction6987
  · exact NewCertificates0218.obstruction6988
  · exact NewCertificates0218.obstruction6989
  · exact NewCertificates0218.obstruction6990
  · exact NewCertificates0218.obstruction6991
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0218.obstruction6992
  · exact NewCertificates0218.obstruction6993
  · exact NewCertificates0218.obstruction6994
  · exact NewCertificates0218.obstruction6995
end Nut8.FiniteSupport149
