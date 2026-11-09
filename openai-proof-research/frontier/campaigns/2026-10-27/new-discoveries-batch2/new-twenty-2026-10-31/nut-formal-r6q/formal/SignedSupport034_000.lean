import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0050.C1620, NewCertificates0050.C1621, NewCertificates0050.C1622, NewCertificates0050.C1623, NewCertificates0050.C1624, NewCertificates0050.C1625, NewCertificates0050.C1626, NewCertificates0050.C1627} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0050.C1628, NewCertificates0050.C1629, NewCertificates0050.C1630, NewCertificates0050.C1631} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0051.C1632, NewCertificates0051.C1633, NewCertificates0051.C1634, NewCertificates0051.C1635, NewCertificates0051.C1636, NewCertificates0051.C1637, NewCertificates0051.C1638, NewCertificates0051.C1639} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0051.C1640, NewCertificates0051.C1641, NewCertificates0051.C1642, NewCertificates0051.C1643, NewCertificates0051.C1644, NewCertificates0051.C1645, NewCertificates0051.C1646, NewCertificates0051.C1647} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0050.obstruction1620
  · exact NewCertificates0050.obstruction1621
  · exact NewCertificates0050.obstruction1622
  · exact NewCertificates0050.obstruction1623
  · exact NewCertificates0050.obstruction1624
  · exact NewCertificates0050.obstruction1625
  · exact NewCertificates0050.obstruction1626
  · exact NewCertificates0050.obstruction1627
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0050.obstruction1628
  · exact NewCertificates0050.obstruction1629
  · exact NewCertificates0050.obstruction1630
  · exact NewCertificates0050.obstruction1631
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0051.obstruction1632
  · exact NewCertificates0051.obstruction1633
  · exact NewCertificates0051.obstruction1634
  · exact NewCertificates0051.obstruction1635
  · exact NewCertificates0051.obstruction1636
  · exact NewCertificates0051.obstruction1637
  · exact NewCertificates0051.obstruction1638
  · exact NewCertificates0051.obstruction1639
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0051.obstruction1640
  · exact NewCertificates0051.obstruction1641
  · exact NewCertificates0051.obstruction1642
  · exact NewCertificates0051.obstruction1643
  · exact NewCertificates0051.obstruction1644
  · exact NewCertificates0051.obstruction1645
  · exact NewCertificates0051.obstruction1646
  · exact NewCertificates0051.obstruction1647
end Nut8.FiniteSupport034
