import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration24 : signedPatterns (U24.submatrix e e) p = {NewCertificates0055.C1762, NewCertificates0055.C1763, NewCertificates0055.C1764, NewCertificates0055.C1765} := by
  decide +kernel
theorem signed_enumeration25 : signedPatterns (U25.submatrix e e) p = {NewCertificates0055.C1766, NewCertificates0055.C1767} := by
  decide +kernel
theorem signed_enumeration26 : signedPatterns (U26.submatrix e e) p = {NewCertificates0055.C1768, NewCertificates0055.C1769, NewCertificates0055.C1770, NewCertificates0055.C1771} := by
  decide +kernel
theorem signed_enumeration27 : signedPatterns (U27.submatrix e e) p = {NewCertificates0055.C1772, NewCertificates0055.C1773} := by
  decide +kernel
theorem checked24 : ∀ A ∈ signedPatterns (U24.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration24]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1762
  · exact NewCertificates0055.obstruction1763
  · exact NewCertificates0055.obstruction1764
  · exact NewCertificates0055.obstruction1765
theorem checked25 : ∀ A ∈ signedPatterns (U25.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration25]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0055.obstruction1766
  · exact NewCertificates0055.obstruction1767
theorem checked26 : ∀ A ∈ signedPatterns (U26.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration26]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1768
  · exact NewCertificates0055.obstruction1769
  · exact NewCertificates0055.obstruction1770
  · exact NewCertificates0055.obstruction1771
theorem checked27 : ∀ A ∈ signedPatterns (U27.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration27]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0055.obstruction1772
  · exact NewCertificates0055.obstruction1773
end Nut8.FiniteSupport034
