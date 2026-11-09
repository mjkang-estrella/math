import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration20 : signedPatterns (U20.submatrix e e) p = {NewCertificates0054.C1748, NewCertificates0054.C1749, NewCertificates0054.C1750, NewCertificates0054.C1751} := by
  decide +kernel
theorem signed_enumeration21 : signedPatterns (U21.submatrix e e) p = {NewCertificates0054.C1752, NewCertificates0054.C1753, NewCertificates0054.C1754, NewCertificates0054.C1755} := by
  decide +kernel
theorem signed_enumeration22 : signedPatterns (U22.submatrix e e) p = {NewCertificates0054.C1756, NewCertificates0054.C1757} := by
  decide +kernel
theorem signed_enumeration23 : signedPatterns (U23.submatrix e e) p = {NewCertificates0054.C1758, NewCertificates0054.C1759, NewCertificates0055.C1760, NewCertificates0055.C1761} := by
  decide +kernel
theorem checked20 : ∀ A ∈ signedPatterns (U20.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration20]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1748
  · exact NewCertificates0054.obstruction1749
  · exact NewCertificates0054.obstruction1750
  · exact NewCertificates0054.obstruction1751
theorem checked21 : ∀ A ∈ signedPatterns (U21.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration21]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1752
  · exact NewCertificates0054.obstruction1753
  · exact NewCertificates0054.obstruction1754
  · exact NewCertificates0054.obstruction1755
theorem checked22 : ∀ A ∈ signedPatterns (U22.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration22]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0054.obstruction1756
  · exact NewCertificates0054.obstruction1757
theorem checked23 : ∀ A ∈ signedPatterns (U23.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration23]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1758
  · exact NewCertificates0054.obstruction1759
  · exact NewCertificates0055.obstruction1760
  · exact NewCertificates0055.obstruction1761
end Nut8.FiniteSupport034
