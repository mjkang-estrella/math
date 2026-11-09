import SupportData027
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport027
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0040.C1292, NewCertificates0040.C1293, NewCertificates0040.C1294, NewCertificates0040.C1295, NewCertificates0040.C1296, NewCertificates0040.C1297, NewCertificates0040.C1298, NewCertificates0040.C1299, NewCertificates0040.C1300, NewCertificates0040.C1301, NewCertificates0040.C1302, NewCertificates0040.C1303, NewCertificates0040.C1304, NewCertificates0040.C1305, NewCertificates0040.C1306, NewCertificates0040.C1307, NewCertificates0040.C1308, NewCertificates0040.C1309, NewCertificates0040.C1310, NewCertificates0040.C1311, NewCertificates0041.C1312, NewCertificates0041.C1313, NewCertificates0041.C1314, NewCertificates0041.C1315, NewCertificates0041.C1316, NewCertificates0041.C1317, NewCertificates0041.C1318, NewCertificates0041.C1319, NewCertificates0041.C1320, NewCertificates0041.C1321, NewCertificates0041.C1322, NewCertificates0041.C1323} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0040.obstruction1292
  · exact NewCertificates0040.obstruction1293
  · exact NewCertificates0040.obstruction1294
  · exact NewCertificates0040.obstruction1295
  · exact NewCertificates0040.obstruction1296
  · exact NewCertificates0040.obstruction1297
  · exact NewCertificates0040.obstruction1298
  · exact NewCertificates0040.obstruction1299
  · exact NewCertificates0040.obstruction1300
  · exact NewCertificates0040.obstruction1301
  · exact NewCertificates0040.obstruction1302
  · exact NewCertificates0040.obstruction1303
  · exact NewCertificates0040.obstruction1304
  · exact NewCertificates0040.obstruction1305
  · exact NewCertificates0040.obstruction1306
  · exact NewCertificates0040.obstruction1307
  · exact NewCertificates0040.obstruction1308
  · exact NewCertificates0040.obstruction1309
  · exact NewCertificates0040.obstruction1310
  · exact NewCertificates0040.obstruction1311
  · exact NewCertificates0041.obstruction1312
  · exact NewCertificates0041.obstruction1313
  · exact NewCertificates0041.obstruction1314
  · exact NewCertificates0041.obstruction1315
  · exact NewCertificates0041.obstruction1316
  · exact NewCertificates0041.obstruction1317
  · exact NewCertificates0041.obstruction1318
  · exact NewCertificates0041.obstruction1319
  · exact NewCertificates0041.obstruction1320
  · exact NewCertificates0041.obstruction1321
  · exact NewCertificates0041.obstruction1322
  · exact NewCertificates0041.obstruction1323
end Nut8.FiniteSupport027
