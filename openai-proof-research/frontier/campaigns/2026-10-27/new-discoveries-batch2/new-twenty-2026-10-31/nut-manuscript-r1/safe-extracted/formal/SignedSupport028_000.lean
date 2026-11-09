import SupportData028
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport028
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0041.C1324, NewCertificates0041.C1325, NewCertificates0041.C1326, NewCertificates0041.C1327, NewCertificates0041.C1328, NewCertificates0041.C1329, NewCertificates0041.C1330, NewCertificates0041.C1331, NewCertificates0041.C1332, NewCertificates0041.C1333, NewCertificates0041.C1334, NewCertificates0041.C1335, NewCertificates0041.C1336, NewCertificates0041.C1337, NewCertificates0041.C1338, NewCertificates0041.C1339} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0041.C1340, NewCertificates0041.C1341, NewCertificates0041.C1342, NewCertificates0041.C1343, NewCertificates0042.C1344, NewCertificates0042.C1345, NewCertificates0042.C1346, NewCertificates0042.C1347} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0042.C1348, NewCertificates0042.C1349, NewCertificates0042.C1350, NewCertificates0042.C1351, NewCertificates0042.C1352, NewCertificates0042.C1353, NewCertificates0042.C1354, NewCertificates0042.C1355, NewCertificates0042.C1356, NewCertificates0042.C1357, NewCertificates0042.C1358, NewCertificates0042.C1359, NewCertificates0042.C1360, NewCertificates0042.C1361, NewCertificates0042.C1362, NewCertificates0042.C1363} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0042.C1364, NewCertificates0042.C1365, NewCertificates0042.C1366, NewCertificates0042.C1367, NewCertificates0042.C1368, NewCertificates0042.C1369, NewCertificates0042.C1370, NewCertificates0042.C1371} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0041.obstruction1324
  · exact NewCertificates0041.obstruction1325
  · exact NewCertificates0041.obstruction1326
  · exact NewCertificates0041.obstruction1327
  · exact NewCertificates0041.obstruction1328
  · exact NewCertificates0041.obstruction1329
  · exact NewCertificates0041.obstruction1330
  · exact NewCertificates0041.obstruction1331
  · exact NewCertificates0041.obstruction1332
  · exact NewCertificates0041.obstruction1333
  · exact NewCertificates0041.obstruction1334
  · exact NewCertificates0041.obstruction1335
  · exact NewCertificates0041.obstruction1336
  · exact NewCertificates0041.obstruction1337
  · exact NewCertificates0041.obstruction1338
  · exact NewCertificates0041.obstruction1339
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0041.obstruction1340
  · exact NewCertificates0041.obstruction1341
  · exact NewCertificates0041.obstruction1342
  · exact NewCertificates0041.obstruction1343
  · exact NewCertificates0042.obstruction1344
  · exact NewCertificates0042.obstruction1345
  · exact NewCertificates0042.obstruction1346
  · exact NewCertificates0042.obstruction1347
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0042.obstruction1348
  · exact NewCertificates0042.obstruction1349
  · exact NewCertificates0042.obstruction1350
  · exact NewCertificates0042.obstruction1351
  · exact NewCertificates0042.obstruction1352
  · exact NewCertificates0042.obstruction1353
  · exact NewCertificates0042.obstruction1354
  · exact NewCertificates0042.obstruction1355
  · exact NewCertificates0042.obstruction1356
  · exact NewCertificates0042.obstruction1357
  · exact NewCertificates0042.obstruction1358
  · exact NewCertificates0042.obstruction1359
  · exact NewCertificates0042.obstruction1360
  · exact NewCertificates0042.obstruction1361
  · exact NewCertificates0042.obstruction1362
  · exact NewCertificates0042.obstruction1363
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0042.obstruction1364
  · exact NewCertificates0042.obstruction1365
  · exact NewCertificates0042.obstruction1366
  · exact NewCertificates0042.obstruction1367
  · exact NewCertificates0042.obstruction1368
  · exact NewCertificates0042.obstruction1369
  · exact NewCertificates0042.obstruction1370
  · exact NewCertificates0042.obstruction1371
end Nut8.FiniteSupport028
