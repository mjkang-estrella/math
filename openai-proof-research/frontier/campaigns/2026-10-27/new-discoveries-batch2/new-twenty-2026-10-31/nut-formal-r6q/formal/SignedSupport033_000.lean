import SupportData033
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport033
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0049.C1588, NewCertificates0049.C1589, NewCertificates0049.C1590, NewCertificates0049.C1591, NewCertificates0049.C1592, NewCertificates0049.C1593, NewCertificates0049.C1594, NewCertificates0049.C1595, NewCertificates0049.C1596, NewCertificates0049.C1597, NewCertificates0049.C1598, NewCertificates0049.C1599, NewCertificates0050.C1600, NewCertificates0050.C1601, NewCertificates0050.C1602, NewCertificates0050.C1603, NewCertificates0050.C1604, NewCertificates0050.C1605, NewCertificates0050.C1606, NewCertificates0050.C1607, NewCertificates0050.C1608, NewCertificates0050.C1609, NewCertificates0050.C1610, NewCertificates0050.C1611, NewCertificates0050.C1612, NewCertificates0050.C1613, NewCertificates0050.C1614, NewCertificates0050.C1615, NewCertificates0050.C1616, NewCertificates0050.C1617, NewCertificates0050.C1618, NewCertificates0050.C1619} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0049.obstruction1588
  · exact NewCertificates0049.obstruction1589
  · exact NewCertificates0049.obstruction1590
  · exact NewCertificates0049.obstruction1591
  · exact NewCertificates0049.obstruction1592
  · exact NewCertificates0049.obstruction1593
  · exact NewCertificates0049.obstruction1594
  · exact NewCertificates0049.obstruction1595
  · exact NewCertificates0049.obstruction1596
  · exact NewCertificates0049.obstruction1597
  · exact NewCertificates0049.obstruction1598
  · exact NewCertificates0049.obstruction1599
  · exact NewCertificates0050.obstruction1600
  · exact NewCertificates0050.obstruction1601
  · exact NewCertificates0050.obstruction1602
  · exact NewCertificates0050.obstruction1603
  · exact NewCertificates0050.obstruction1604
  · exact NewCertificates0050.obstruction1605
  · exact NewCertificates0050.obstruction1606
  · exact NewCertificates0050.obstruction1607
  · exact NewCertificates0050.obstruction1608
  · exact NewCertificates0050.obstruction1609
  · exact NewCertificates0050.obstruction1610
  · exact NewCertificates0050.obstruction1611
  · exact NewCertificates0050.obstruction1612
  · exact NewCertificates0050.obstruction1613
  · exact NewCertificates0050.obstruction1614
  · exact NewCertificates0050.obstruction1615
  · exact NewCertificates0050.obstruction1616
  · exact NewCertificates0050.obstruction1617
  · exact NewCertificates0050.obstruction1618
  · exact NewCertificates0050.obstruction1619
end Nut8.FiniteSupport033
