import SupportData032
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport032
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0047.C1532, NewCertificates0047.C1533, NewCertificates0047.C1534, NewCertificates0047.C1535, NewCertificates0048.C1536, NewCertificates0048.C1537, NewCertificates0048.C1538, NewCertificates0048.C1539, NewCertificates0048.C1540, NewCertificates0048.C1541, NewCertificates0048.C1542, NewCertificates0048.C1543, NewCertificates0048.C1544, NewCertificates0048.C1545, NewCertificates0048.C1546, NewCertificates0048.C1547} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0048.C1548, NewCertificates0048.C1549, NewCertificates0048.C1550, NewCertificates0048.C1551, NewCertificates0048.C1552, NewCertificates0048.C1553, NewCertificates0048.C1554, NewCertificates0048.C1555, NewCertificates0048.C1556, NewCertificates0048.C1557, NewCertificates0048.C1558, NewCertificates0048.C1559, NewCertificates0048.C1560, NewCertificates0048.C1561, NewCertificates0048.C1562, NewCertificates0048.C1563} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0048.C1564, NewCertificates0048.C1565, NewCertificates0048.C1566, NewCertificates0048.C1567, NewCertificates0049.C1568, NewCertificates0049.C1569, NewCertificates0049.C1570, NewCertificates0049.C1571, NewCertificates0049.C1572, NewCertificates0049.C1573, NewCertificates0049.C1574, NewCertificates0049.C1575, NewCertificates0049.C1576, NewCertificates0049.C1577, NewCertificates0049.C1578, NewCertificates0049.C1579} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0049.C1580, NewCertificates0049.C1581, NewCertificates0049.C1582, NewCertificates0049.C1583, NewCertificates0049.C1584, NewCertificates0049.C1585, NewCertificates0049.C1586, NewCertificates0049.C1587} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0047.obstruction1532
  · exact NewCertificates0047.obstruction1533
  · exact NewCertificates0047.obstruction1534
  · exact NewCertificates0047.obstruction1535
  · exact NewCertificates0048.obstruction1536
  · exact NewCertificates0048.obstruction1537
  · exact NewCertificates0048.obstruction1538
  · exact NewCertificates0048.obstruction1539
  · exact NewCertificates0048.obstruction1540
  · exact NewCertificates0048.obstruction1541
  · exact NewCertificates0048.obstruction1542
  · exact NewCertificates0048.obstruction1543
  · exact NewCertificates0048.obstruction1544
  · exact NewCertificates0048.obstruction1545
  · exact NewCertificates0048.obstruction1546
  · exact NewCertificates0048.obstruction1547
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0048.obstruction1548
  · exact NewCertificates0048.obstruction1549
  · exact NewCertificates0048.obstruction1550
  · exact NewCertificates0048.obstruction1551
  · exact NewCertificates0048.obstruction1552
  · exact NewCertificates0048.obstruction1553
  · exact NewCertificates0048.obstruction1554
  · exact NewCertificates0048.obstruction1555
  · exact NewCertificates0048.obstruction1556
  · exact NewCertificates0048.obstruction1557
  · exact NewCertificates0048.obstruction1558
  · exact NewCertificates0048.obstruction1559
  · exact NewCertificates0048.obstruction1560
  · exact NewCertificates0048.obstruction1561
  · exact NewCertificates0048.obstruction1562
  · exact NewCertificates0048.obstruction1563
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0048.obstruction1564
  · exact NewCertificates0048.obstruction1565
  · exact NewCertificates0048.obstruction1566
  · exact NewCertificates0048.obstruction1567
  · exact NewCertificates0049.obstruction1568
  · exact NewCertificates0049.obstruction1569
  · exact NewCertificates0049.obstruction1570
  · exact NewCertificates0049.obstruction1571
  · exact NewCertificates0049.obstruction1572
  · exact NewCertificates0049.obstruction1573
  · exact NewCertificates0049.obstruction1574
  · exact NewCertificates0049.obstruction1575
  · exact NewCertificates0049.obstruction1576
  · exact NewCertificates0049.obstruction1577
  · exact NewCertificates0049.obstruction1578
  · exact NewCertificates0049.obstruction1579
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0049.obstruction1580
  · exact NewCertificates0049.obstruction1581
  · exact NewCertificates0049.obstruction1582
  · exact NewCertificates0049.obstruction1583
  · exact NewCertificates0049.obstruction1584
  · exact NewCertificates0049.obstruction1585
  · exact NewCertificates0049.obstruction1586
  · exact NewCertificates0049.obstruction1587
end Nut8.FiniteSupport032
