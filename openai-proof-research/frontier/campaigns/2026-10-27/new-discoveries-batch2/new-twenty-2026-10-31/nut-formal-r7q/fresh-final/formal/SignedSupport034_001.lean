import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0051.C1648, NewCertificates0051.C1649, NewCertificates0051.C1650, NewCertificates0051.C1651} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0051.C1652, NewCertificates0051.C1653, NewCertificates0051.C1654, NewCertificates0051.C1655, NewCertificates0051.C1656, NewCertificates0051.C1657, NewCertificates0051.C1658, NewCertificates0051.C1659} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0051.C1660, NewCertificates0051.C1661, NewCertificates0051.C1662, NewCertificates0051.C1663} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0052.C1664, NewCertificates0052.C1665, NewCertificates0052.C1666, NewCertificates0052.C1667, NewCertificates0052.C1668, NewCertificates0052.C1669, NewCertificates0052.C1670, NewCertificates0052.C1671} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0051.obstruction1648
  · exact NewCertificates0051.obstruction1649
  · exact NewCertificates0051.obstruction1650
  · exact NewCertificates0051.obstruction1651
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0051.obstruction1652
  · exact NewCertificates0051.obstruction1653
  · exact NewCertificates0051.obstruction1654
  · exact NewCertificates0051.obstruction1655
  · exact NewCertificates0051.obstruction1656
  · exact NewCertificates0051.obstruction1657
  · exact NewCertificates0051.obstruction1658
  · exact NewCertificates0051.obstruction1659
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0051.obstruction1660
  · exact NewCertificates0051.obstruction1661
  · exact NewCertificates0051.obstruction1662
  · exact NewCertificates0051.obstruction1663
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0052.obstruction1664
  · exact NewCertificates0052.obstruction1665
  · exact NewCertificates0052.obstruction1666
  · exact NewCertificates0052.obstruction1667
  · exact NewCertificates0052.obstruction1668
  · exact NewCertificates0052.obstruction1669
  · exact NewCertificates0052.obstruction1670
  · exact NewCertificates0052.obstruction1671
end Nut8.FiniteSupport034
