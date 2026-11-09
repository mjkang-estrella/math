import SupportData029
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport029
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0044.C1420, NewCertificates0044.C1421, NewCertificates0044.C1422, NewCertificates0044.C1423, NewCertificates0044.C1424, NewCertificates0044.C1425, NewCertificates0044.C1426, NewCertificates0044.C1427, NewCertificates0044.C1428, NewCertificates0044.C1429, NewCertificates0044.C1430, NewCertificates0044.C1431, NewCertificates0044.C1432, NewCertificates0044.C1433, NewCertificates0044.C1434, NewCertificates0044.C1435, NewCertificates0044.C1436, NewCertificates0044.C1437, NewCertificates0044.C1438, NewCertificates0044.C1439, NewCertificates0045.C1440, NewCertificates0045.C1441, NewCertificates0045.C1442, NewCertificates0045.C1443, NewCertificates0045.C1444, NewCertificates0045.C1445, NewCertificates0045.C1446, NewCertificates0045.C1447, NewCertificates0045.C1448, NewCertificates0045.C1449, NewCertificates0045.C1450, NewCertificates0045.C1451} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0045.C1452, NewCertificates0045.C1453, NewCertificates0045.C1454, NewCertificates0045.C1455, NewCertificates0045.C1456, NewCertificates0045.C1457, NewCertificates0045.C1458, NewCertificates0045.C1459, NewCertificates0045.C1460, NewCertificates0045.C1461, NewCertificates0045.C1462, NewCertificates0045.C1463, NewCertificates0045.C1464, NewCertificates0045.C1465, NewCertificates0045.C1466, NewCertificates0045.C1467} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0044.obstruction1420
  · exact NewCertificates0044.obstruction1421
  · exact NewCertificates0044.obstruction1422
  · exact NewCertificates0044.obstruction1423
  · exact NewCertificates0044.obstruction1424
  · exact NewCertificates0044.obstruction1425
  · exact NewCertificates0044.obstruction1426
  · exact NewCertificates0044.obstruction1427
  · exact NewCertificates0044.obstruction1428
  · exact NewCertificates0044.obstruction1429
  · exact NewCertificates0044.obstruction1430
  · exact NewCertificates0044.obstruction1431
  · exact NewCertificates0044.obstruction1432
  · exact NewCertificates0044.obstruction1433
  · exact NewCertificates0044.obstruction1434
  · exact NewCertificates0044.obstruction1435
  · exact NewCertificates0044.obstruction1436
  · exact NewCertificates0044.obstruction1437
  · exact NewCertificates0044.obstruction1438
  · exact NewCertificates0044.obstruction1439
  · exact NewCertificates0045.obstruction1440
  · exact NewCertificates0045.obstruction1441
  · exact NewCertificates0045.obstruction1442
  · exact NewCertificates0045.obstruction1443
  · exact NewCertificates0045.obstruction1444
  · exact NewCertificates0045.obstruction1445
  · exact NewCertificates0045.obstruction1446
  · exact NewCertificates0045.obstruction1447
  · exact NewCertificates0045.obstruction1448
  · exact NewCertificates0045.obstruction1449
  · exact NewCertificates0045.obstruction1450
  · exact NewCertificates0045.obstruction1451
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0045.obstruction1452
  · exact NewCertificates0045.obstruction1453
  · exact NewCertificates0045.obstruction1454
  · exact NewCertificates0045.obstruction1455
  · exact NewCertificates0045.obstruction1456
  · exact NewCertificates0045.obstruction1457
  · exact NewCertificates0045.obstruction1458
  · exact NewCertificates0045.obstruction1459
  · exact NewCertificates0045.obstruction1460
  · exact NewCertificates0045.obstruction1461
  · exact NewCertificates0045.obstruction1462
  · exact NewCertificates0045.obstruction1463
  · exact NewCertificates0045.obstruction1464
  · exact NewCertificates0045.obstruction1465
  · exact NewCertificates0045.obstruction1466
  · exact NewCertificates0045.obstruction1467
end Nut8.FiniteSupport029
