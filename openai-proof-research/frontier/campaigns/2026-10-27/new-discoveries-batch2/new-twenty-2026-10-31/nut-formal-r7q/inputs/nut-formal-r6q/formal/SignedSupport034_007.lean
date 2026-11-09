import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration28 : signedPatterns (U28.submatrix e e) p = {NewCertificates0055.C1774, NewCertificates0055.C1775, NewCertificates0055.C1776, NewCertificates0055.C1777} := by
  decide +kernel
theorem signed_enumeration29 : signedPatterns (U29.submatrix e e) p = {NewCertificates0055.C1778, NewCertificates0055.C1779, NewCertificates0055.C1780, NewCertificates0055.C1781} := by
  decide +kernel
theorem signed_enumeration30 : signedPatterns (U30.submatrix e e) p = {NewCertificates0055.C1782, NewCertificates0055.C1783} := by
  decide +kernel
theorem signed_enumeration31 : signedPatterns (U31.submatrix e e) p = {NewCertificates0055.C1784, NewCertificates0055.C1785, NewCertificates0055.C1786, NewCertificates0055.C1787} := by
  decide +kernel
theorem checked28 : ∀ A ∈ signedPatterns (U28.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration28]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1774
  · exact NewCertificates0055.obstruction1775
  · exact NewCertificates0055.obstruction1776
  · exact NewCertificates0055.obstruction1777
theorem checked29 : ∀ A ∈ signedPatterns (U29.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration29]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1778
  · exact NewCertificates0055.obstruction1779
  · exact NewCertificates0055.obstruction1780
  · exact NewCertificates0055.obstruction1781
theorem checked30 : ∀ A ∈ signedPatterns (U30.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration30]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0055.obstruction1782
  · exact NewCertificates0055.obstruction1783
theorem checked31 : ∀ A ∈ signedPatterns (U31.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration31]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1784
  · exact NewCertificates0055.obstruction1785
  · exact NewCertificates0055.obstruction1786
  · exact NewCertificates0055.obstruction1787
end Nut8.FiniteSupport034
