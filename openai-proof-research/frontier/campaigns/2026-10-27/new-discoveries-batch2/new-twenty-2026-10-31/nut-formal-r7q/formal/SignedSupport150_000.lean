import SupportData150
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport150
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0218.C6996, NewCertificates0218.C6997, NewCertificates0218.C6998, NewCertificates0218.C6999, NewCertificates0218.C7000, NewCertificates0218.C7001, NewCertificates0218.C7002, NewCertificates0218.C7003} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0218.C7004, NewCertificates0218.C7005, NewCertificates0218.C7006, NewCertificates0218.C7007, NewCertificates0219.C7008, NewCertificates0219.C7009, NewCertificates0219.C7010, NewCertificates0219.C7011} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0219.C7012, NewCertificates0219.C7013, NewCertificates0219.C7014, NewCertificates0219.C7015, NewCertificates0219.C7016, NewCertificates0219.C7017, NewCertificates0219.C7018, NewCertificates0219.C7019} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0219.C7020, NewCertificates0219.C7021, NewCertificates0219.C7022, NewCertificates0219.C7023, NewCertificates0219.C7024, NewCertificates0219.C7025, NewCertificates0219.C7026, NewCertificates0219.C7027} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0218.obstruction6996
  · exact NewCertificates0218.obstruction6997
  · exact NewCertificates0218.obstruction6998
  · exact NewCertificates0218.obstruction6999
  · exact NewCertificates0218.obstruction7000
  · exact NewCertificates0218.obstruction7001
  · exact NewCertificates0218.obstruction7002
  · exact NewCertificates0218.obstruction7003
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0218.obstruction7004
  · exact NewCertificates0218.obstruction7005
  · exact NewCertificates0218.obstruction7006
  · exact NewCertificates0218.obstruction7007
  · exact NewCertificates0219.obstruction7008
  · exact NewCertificates0219.obstruction7009
  · exact NewCertificates0219.obstruction7010
  · exact NewCertificates0219.obstruction7011
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0219.obstruction7012
  · exact NewCertificates0219.obstruction7013
  · exact NewCertificates0219.obstruction7014
  · exact NewCertificates0219.obstruction7015
  · exact NewCertificates0219.obstruction7016
  · exact NewCertificates0219.obstruction7017
  · exact NewCertificates0219.obstruction7018
  · exact NewCertificates0219.obstruction7019
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0219.obstruction7020
  · exact NewCertificates0219.obstruction7021
  · exact NewCertificates0219.obstruction7022
  · exact NewCertificates0219.obstruction7023
  · exact NewCertificates0219.obstruction7024
  · exact NewCertificates0219.obstruction7025
  · exact NewCertificates0219.obstruction7026
  · exact NewCertificates0219.obstruction7027
end Nut8.FiniteSupport150
