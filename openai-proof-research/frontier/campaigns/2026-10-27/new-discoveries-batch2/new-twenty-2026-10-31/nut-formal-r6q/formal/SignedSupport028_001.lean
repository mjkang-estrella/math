import SupportData028
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport028
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0042.C1372, NewCertificates0042.C1373, NewCertificates0042.C1374, NewCertificates0042.C1375} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0043.C1376, NewCertificates0043.C1377, NewCertificates0043.C1378, NewCertificates0043.C1379, NewCertificates0043.C1380, NewCertificates0043.C1381, NewCertificates0043.C1382, NewCertificates0043.C1383} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0043.C1384, NewCertificates0043.C1385, NewCertificates0043.C1386, NewCertificates0043.C1387, NewCertificates0043.C1388, NewCertificates0043.C1389, NewCertificates0043.C1390, NewCertificates0043.C1391, NewCertificates0043.C1392, NewCertificates0043.C1393, NewCertificates0043.C1394, NewCertificates0043.C1395, NewCertificates0043.C1396, NewCertificates0043.C1397, NewCertificates0043.C1398, NewCertificates0043.C1399} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0043.C1400, NewCertificates0043.C1401, NewCertificates0043.C1402, NewCertificates0043.C1403, NewCertificates0043.C1404, NewCertificates0043.C1405, NewCertificates0043.C1406, NewCertificates0043.C1407} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0042.obstruction1372
  · exact NewCertificates0042.obstruction1373
  · exact NewCertificates0042.obstruction1374
  · exact NewCertificates0042.obstruction1375
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0043.obstruction1376
  · exact NewCertificates0043.obstruction1377
  · exact NewCertificates0043.obstruction1378
  · exact NewCertificates0043.obstruction1379
  · exact NewCertificates0043.obstruction1380
  · exact NewCertificates0043.obstruction1381
  · exact NewCertificates0043.obstruction1382
  · exact NewCertificates0043.obstruction1383
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0043.obstruction1384
  · exact NewCertificates0043.obstruction1385
  · exact NewCertificates0043.obstruction1386
  · exact NewCertificates0043.obstruction1387
  · exact NewCertificates0043.obstruction1388
  · exact NewCertificates0043.obstruction1389
  · exact NewCertificates0043.obstruction1390
  · exact NewCertificates0043.obstruction1391
  · exact NewCertificates0043.obstruction1392
  · exact NewCertificates0043.obstruction1393
  · exact NewCertificates0043.obstruction1394
  · exact NewCertificates0043.obstruction1395
  · exact NewCertificates0043.obstruction1396
  · exact NewCertificates0043.obstruction1397
  · exact NewCertificates0043.obstruction1398
  · exact NewCertificates0043.obstruction1399
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0043.obstruction1400
  · exact NewCertificates0043.obstruction1401
  · exact NewCertificates0043.obstruction1402
  · exact NewCertificates0043.obstruction1403
  · exact NewCertificates0043.obstruction1404
  · exact NewCertificates0043.obstruction1405
  · exact NewCertificates0043.obstruction1406
  · exact NewCertificates0043.obstruction1407
end Nut8.FiniteSupport028
