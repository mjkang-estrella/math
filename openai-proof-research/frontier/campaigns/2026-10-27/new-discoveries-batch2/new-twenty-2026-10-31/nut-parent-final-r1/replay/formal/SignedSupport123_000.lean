import SupportData123
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport123
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0186.C5972, NewCertificates0186.C5973, NewCertificates0186.C5974, NewCertificates0186.C5975, NewCertificates0186.C5976, NewCertificates0186.C5977, NewCertificates0186.C5978, NewCertificates0186.C5979} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0186.C5980, NewCertificates0186.C5981, NewCertificates0186.C5982, NewCertificates0186.C5983, NewCertificates0187.C5984, NewCertificates0187.C5985, NewCertificates0187.C5986, NewCertificates0187.C5987} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0187.C5988, NewCertificates0187.C5989, NewCertificates0187.C5990, NewCertificates0187.C5991, NewCertificates0187.C5992, NewCertificates0187.C5993, NewCertificates0187.C5994, NewCertificates0187.C5995} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0187.C5996, NewCertificates0187.C5997, NewCertificates0187.C5998, NewCertificates0187.C5999, NewCertificates0187.C6000, NewCertificates0187.C6001, NewCertificates0187.C6002, NewCertificates0187.C6003} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5972
  · exact NewCertificates0186.obstruction5973
  · exact NewCertificates0186.obstruction5974
  · exact NewCertificates0186.obstruction5975
  · exact NewCertificates0186.obstruction5976
  · exact NewCertificates0186.obstruction5977
  · exact NewCertificates0186.obstruction5978
  · exact NewCertificates0186.obstruction5979
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5980
  · exact NewCertificates0186.obstruction5981
  · exact NewCertificates0186.obstruction5982
  · exact NewCertificates0186.obstruction5983
  · exact NewCertificates0187.obstruction5984
  · exact NewCertificates0187.obstruction5985
  · exact NewCertificates0187.obstruction5986
  · exact NewCertificates0187.obstruction5987
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0187.obstruction5988
  · exact NewCertificates0187.obstruction5989
  · exact NewCertificates0187.obstruction5990
  · exact NewCertificates0187.obstruction5991
  · exact NewCertificates0187.obstruction5992
  · exact NewCertificates0187.obstruction5993
  · exact NewCertificates0187.obstruction5994
  · exact NewCertificates0187.obstruction5995
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0187.obstruction5996
  · exact NewCertificates0187.obstruction5997
  · exact NewCertificates0187.obstruction5998
  · exact NewCertificates0187.obstruction5999
  · exact NewCertificates0187.obstruction6000
  · exact NewCertificates0187.obstruction6001
  · exact NewCertificates0187.obstruction6002
  · exact NewCertificates0187.obstruction6003
end Nut8.FiniteSupport123
