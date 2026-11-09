import SupportData026
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport026
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0038.C1220, NewCertificates0038.C1221, NewCertificates0038.C1222, NewCertificates0038.C1223, NewCertificates0038.C1224, NewCertificates0038.C1225, NewCertificates0038.C1226, NewCertificates0038.C1227, NewCertificates0038.C1228, NewCertificates0038.C1229, NewCertificates0038.C1230, NewCertificates0038.C1231, NewCertificates0038.C1232, NewCertificates0038.C1233, NewCertificates0038.C1234, NewCertificates0038.C1235, NewCertificates0038.C1236, NewCertificates0038.C1237, NewCertificates0038.C1238, NewCertificates0038.C1239, NewCertificates0038.C1240, NewCertificates0038.C1241, NewCertificates0038.C1242, NewCertificates0038.C1243, NewCertificates0038.C1244, NewCertificates0038.C1245, NewCertificates0038.C1246, NewCertificates0038.C1247, NewCertificates0039.C1248, NewCertificates0039.C1249, NewCertificates0039.C1250, NewCertificates0039.C1251} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0039.C1252, NewCertificates0039.C1253, NewCertificates0039.C1254, NewCertificates0039.C1255, NewCertificates0039.C1256, NewCertificates0039.C1257, NewCertificates0039.C1258, NewCertificates0039.C1259, NewCertificates0039.C1260, NewCertificates0039.C1261, NewCertificates0039.C1262, NewCertificates0039.C1263, NewCertificates0039.C1264, NewCertificates0039.C1265, NewCertificates0039.C1266, NewCertificates0039.C1267} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0039.C1268, NewCertificates0039.C1269, NewCertificates0039.C1270, NewCertificates0039.C1271, NewCertificates0039.C1272, NewCertificates0039.C1273, NewCertificates0039.C1274, NewCertificates0039.C1275, NewCertificates0039.C1276, NewCertificates0039.C1277, NewCertificates0039.C1278, NewCertificates0039.C1279, NewCertificates0040.C1280, NewCertificates0040.C1281, NewCertificates0040.C1282, NewCertificates0040.C1283} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0040.C1284, NewCertificates0040.C1285, NewCertificates0040.C1286, NewCertificates0040.C1287, NewCertificates0040.C1288, NewCertificates0040.C1289, NewCertificates0040.C1290, NewCertificates0040.C1291} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0038.obstruction1220
  · exact NewCertificates0038.obstruction1221
  · exact NewCertificates0038.obstruction1222
  · exact NewCertificates0038.obstruction1223
  · exact NewCertificates0038.obstruction1224
  · exact NewCertificates0038.obstruction1225
  · exact NewCertificates0038.obstruction1226
  · exact NewCertificates0038.obstruction1227
  · exact NewCertificates0038.obstruction1228
  · exact NewCertificates0038.obstruction1229
  · exact NewCertificates0038.obstruction1230
  · exact NewCertificates0038.obstruction1231
  · exact NewCertificates0038.obstruction1232
  · exact NewCertificates0038.obstruction1233
  · exact NewCertificates0038.obstruction1234
  · exact NewCertificates0038.obstruction1235
  · exact NewCertificates0038.obstruction1236
  · exact NewCertificates0038.obstruction1237
  · exact NewCertificates0038.obstruction1238
  · exact NewCertificates0038.obstruction1239
  · exact NewCertificates0038.obstruction1240
  · exact NewCertificates0038.obstruction1241
  · exact NewCertificates0038.obstruction1242
  · exact NewCertificates0038.obstruction1243
  · exact NewCertificates0038.obstruction1244
  · exact NewCertificates0038.obstruction1245
  · exact NewCertificates0038.obstruction1246
  · exact NewCertificates0038.obstruction1247
  · exact NewCertificates0039.obstruction1248
  · exact NewCertificates0039.obstruction1249
  · exact NewCertificates0039.obstruction1250
  · exact NewCertificates0039.obstruction1251
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0039.obstruction1252
  · exact NewCertificates0039.obstruction1253
  · exact NewCertificates0039.obstruction1254
  · exact NewCertificates0039.obstruction1255
  · exact NewCertificates0039.obstruction1256
  · exact NewCertificates0039.obstruction1257
  · exact NewCertificates0039.obstruction1258
  · exact NewCertificates0039.obstruction1259
  · exact NewCertificates0039.obstruction1260
  · exact NewCertificates0039.obstruction1261
  · exact NewCertificates0039.obstruction1262
  · exact NewCertificates0039.obstruction1263
  · exact NewCertificates0039.obstruction1264
  · exact NewCertificates0039.obstruction1265
  · exact NewCertificates0039.obstruction1266
  · exact NewCertificates0039.obstruction1267
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0039.obstruction1268
  · exact NewCertificates0039.obstruction1269
  · exact NewCertificates0039.obstruction1270
  · exact NewCertificates0039.obstruction1271
  · exact NewCertificates0039.obstruction1272
  · exact NewCertificates0039.obstruction1273
  · exact NewCertificates0039.obstruction1274
  · exact NewCertificates0039.obstruction1275
  · exact NewCertificates0039.obstruction1276
  · exact NewCertificates0039.obstruction1277
  · exact NewCertificates0039.obstruction1278
  · exact NewCertificates0039.obstruction1279
  · exact NewCertificates0040.obstruction1280
  · exact NewCertificates0040.obstruction1281
  · exact NewCertificates0040.obstruction1282
  · exact NewCertificates0040.obstruction1283
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0040.obstruction1284
  · exact NewCertificates0040.obstruction1285
  · exact NewCertificates0040.obstruction1286
  · exact NewCertificates0040.obstruction1287
  · exact NewCertificates0040.obstruction1288
  · exact NewCertificates0040.obstruction1289
  · exact NewCertificates0040.obstruction1290
  · exact NewCertificates0040.obstruction1291
end Nut8.FiniteSupport026
