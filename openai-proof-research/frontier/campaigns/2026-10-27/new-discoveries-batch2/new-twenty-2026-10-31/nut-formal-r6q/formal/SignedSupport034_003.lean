import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0053.C1700, NewCertificates0053.C1701, NewCertificates0053.C1702, NewCertificates0053.C1703} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0053.C1704, NewCertificates0053.C1705, NewCertificates0053.C1706, NewCertificates0053.C1707, NewCertificates0053.C1708, NewCertificates0053.C1709, NewCertificates0053.C1710, NewCertificates0053.C1711} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0053.C1712, NewCertificates0053.C1713, NewCertificates0053.C1714, NewCertificates0053.C1715} := by
  decide +kernel
theorem signed_enumeration15 : signedPatterns (U15.submatrix e e) p = {NewCertificates0053.C1716, NewCertificates0053.C1717, NewCertificates0053.C1718, NewCertificates0053.C1719, NewCertificates0053.C1720, NewCertificates0053.C1721, NewCertificates0053.C1722, NewCertificates0053.C1723} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0053.obstruction1700
  · exact NewCertificates0053.obstruction1701
  · exact NewCertificates0053.obstruction1702
  · exact NewCertificates0053.obstruction1703
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0053.obstruction1704
  · exact NewCertificates0053.obstruction1705
  · exact NewCertificates0053.obstruction1706
  · exact NewCertificates0053.obstruction1707
  · exact NewCertificates0053.obstruction1708
  · exact NewCertificates0053.obstruction1709
  · exact NewCertificates0053.obstruction1710
  · exact NewCertificates0053.obstruction1711
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0053.obstruction1712
  · exact NewCertificates0053.obstruction1713
  · exact NewCertificates0053.obstruction1714
  · exact NewCertificates0053.obstruction1715
theorem checked15 : ∀ A ∈ signedPatterns (U15.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration15]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0053.obstruction1716
  · exact NewCertificates0053.obstruction1717
  · exact NewCertificates0053.obstruction1718
  · exact NewCertificates0053.obstruction1719
  · exact NewCertificates0053.obstruction1720
  · exact NewCertificates0053.obstruction1721
  · exact NewCertificates0053.obstruction1722
  · exact NewCertificates0053.obstruction1723
end Nut8.FiniteSupport034
