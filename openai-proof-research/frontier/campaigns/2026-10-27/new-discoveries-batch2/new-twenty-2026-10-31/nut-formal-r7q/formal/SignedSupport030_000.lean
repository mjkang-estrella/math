import SupportData030
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport030
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0045.C1468, NewCertificates0045.C1469, NewCertificates0045.C1470, NewCertificates0045.C1471, NewCertificates0046.C1472, NewCertificates0046.C1473, NewCertificates0046.C1474, NewCertificates0046.C1475, NewCertificates0046.C1476, NewCertificates0046.C1477, NewCertificates0046.C1478, NewCertificates0046.C1479, NewCertificates0046.C1480, NewCertificates0046.C1481, NewCertificates0046.C1482, NewCertificates0046.C1483, NewCertificates0046.C1484, NewCertificates0046.C1485, NewCertificates0046.C1486, NewCertificates0046.C1487, NewCertificates0046.C1488, NewCertificates0046.C1489, NewCertificates0046.C1490, NewCertificates0046.C1491, NewCertificates0046.C1492, NewCertificates0046.C1493, NewCertificates0046.C1494, NewCertificates0046.C1495, NewCertificates0046.C1496, NewCertificates0046.C1497, NewCertificates0046.C1498, NewCertificates0046.C1499} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0045.obstruction1468
  · exact NewCertificates0045.obstruction1469
  · exact NewCertificates0045.obstruction1470
  · exact NewCertificates0045.obstruction1471
  · exact NewCertificates0046.obstruction1472
  · exact NewCertificates0046.obstruction1473
  · exact NewCertificates0046.obstruction1474
  · exact NewCertificates0046.obstruction1475
  · exact NewCertificates0046.obstruction1476
  · exact NewCertificates0046.obstruction1477
  · exact NewCertificates0046.obstruction1478
  · exact NewCertificates0046.obstruction1479
  · exact NewCertificates0046.obstruction1480
  · exact NewCertificates0046.obstruction1481
  · exact NewCertificates0046.obstruction1482
  · exact NewCertificates0046.obstruction1483
  · exact NewCertificates0046.obstruction1484
  · exact NewCertificates0046.obstruction1485
  · exact NewCertificates0046.obstruction1486
  · exact NewCertificates0046.obstruction1487
  · exact NewCertificates0046.obstruction1488
  · exact NewCertificates0046.obstruction1489
  · exact NewCertificates0046.obstruction1490
  · exact NewCertificates0046.obstruction1491
  · exact NewCertificates0046.obstruction1492
  · exact NewCertificates0046.obstruction1493
  · exact NewCertificates0046.obstruction1494
  · exact NewCertificates0046.obstruction1495
  · exact NewCertificates0046.obstruction1496
  · exact NewCertificates0046.obstruction1497
  · exact NewCertificates0046.obstruction1498
  · exact NewCertificates0046.obstruction1499
end Nut8.FiniteSupport030
