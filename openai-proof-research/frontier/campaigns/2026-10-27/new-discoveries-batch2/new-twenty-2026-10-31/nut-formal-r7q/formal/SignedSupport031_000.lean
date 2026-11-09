import SupportData031
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport031
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0046.C1500, NewCertificates0046.C1501, NewCertificates0046.C1502, NewCertificates0046.C1503, NewCertificates0047.C1504, NewCertificates0047.C1505, NewCertificates0047.C1506, NewCertificates0047.C1507, NewCertificates0047.C1508, NewCertificates0047.C1509, NewCertificates0047.C1510, NewCertificates0047.C1511, NewCertificates0047.C1512, NewCertificates0047.C1513, NewCertificates0047.C1514, NewCertificates0047.C1515, NewCertificates0047.C1516, NewCertificates0047.C1517, NewCertificates0047.C1518, NewCertificates0047.C1519, NewCertificates0047.C1520, NewCertificates0047.C1521, NewCertificates0047.C1522, NewCertificates0047.C1523, NewCertificates0047.C1524, NewCertificates0047.C1525, NewCertificates0047.C1526, NewCertificates0047.C1527, NewCertificates0047.C1528, NewCertificates0047.C1529, NewCertificates0047.C1530, NewCertificates0047.C1531} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0046.obstruction1500
  · exact NewCertificates0046.obstruction1501
  · exact NewCertificates0046.obstruction1502
  · exact NewCertificates0046.obstruction1503
  · exact NewCertificates0047.obstruction1504
  · exact NewCertificates0047.obstruction1505
  · exact NewCertificates0047.obstruction1506
  · exact NewCertificates0047.obstruction1507
  · exact NewCertificates0047.obstruction1508
  · exact NewCertificates0047.obstruction1509
  · exact NewCertificates0047.obstruction1510
  · exact NewCertificates0047.obstruction1511
  · exact NewCertificates0047.obstruction1512
  · exact NewCertificates0047.obstruction1513
  · exact NewCertificates0047.obstruction1514
  · exact NewCertificates0047.obstruction1515
  · exact NewCertificates0047.obstruction1516
  · exact NewCertificates0047.obstruction1517
  · exact NewCertificates0047.obstruction1518
  · exact NewCertificates0047.obstruction1519
  · exact NewCertificates0047.obstruction1520
  · exact NewCertificates0047.obstruction1521
  · exact NewCertificates0047.obstruction1522
  · exact NewCertificates0047.obstruction1523
  · exact NewCertificates0047.obstruction1524
  · exact NewCertificates0047.obstruction1525
  · exact NewCertificates0047.obstruction1526
  · exact NewCertificates0047.obstruction1527
  · exact NewCertificates0047.obstruction1528
  · exact NewCertificates0047.obstruction1529
  · exact NewCertificates0047.obstruction1530
  · exact NewCertificates0047.obstruction1531
end Nut8.FiniteSupport031
