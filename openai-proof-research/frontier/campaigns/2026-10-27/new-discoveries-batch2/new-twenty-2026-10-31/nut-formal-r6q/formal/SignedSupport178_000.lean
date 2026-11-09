import SupportData178
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport178
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0259.C8308, NewCertificates0259.C8309, NewCertificates0259.C8310, NewCertificates0259.C8311, NewCertificates0259.C8312, NewCertificates0259.C8313, NewCertificates0259.C8314, NewCertificates0259.C8315, NewCertificates0259.C8316, NewCertificates0259.C8317, NewCertificates0259.C8318, NewCertificates0259.C8319, NewCertificates0260.C8320, NewCertificates0260.C8321, NewCertificates0260.C8322, NewCertificates0260.C8323, NewCertificates0260.C8324, NewCertificates0260.C8325, NewCertificates0260.C8326, NewCertificates0260.C8327, NewCertificates0260.C8328, NewCertificates0260.C8329, NewCertificates0260.C8330, NewCertificates0260.C8331, NewCertificates0260.C8332, NewCertificates0260.C8333, NewCertificates0260.C8334, NewCertificates0260.C8335, NewCertificates0260.C8336, NewCertificates0260.C8337, NewCertificates0260.C8338, NewCertificates0260.C8339} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0260.C8340, NewCertificates0260.C8341, NewCertificates0260.C8342, NewCertificates0260.C8343, NewCertificates0260.C8344, NewCertificates0260.C8345, NewCertificates0260.C8346, NewCertificates0260.C8347, NewCertificates0260.C8348, NewCertificates0260.C8349, NewCertificates0260.C8350, NewCertificates0260.C8351, NewCertificates0261.C8352, NewCertificates0261.C8353, NewCertificates0261.C8354, NewCertificates0261.C8355} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0261.C8356, NewCertificates0261.C8357, NewCertificates0261.C8358, NewCertificates0261.C8359, NewCertificates0261.C8360, NewCertificates0261.C8361, NewCertificates0261.C8362, NewCertificates0261.C8363, NewCertificates0261.C8364, NewCertificates0261.C8365, NewCertificates0261.C8366, NewCertificates0261.C8367, NewCertificates0261.C8368, NewCertificates0261.C8369, NewCertificates0261.C8370, NewCertificates0261.C8371} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0261.C8372, NewCertificates0261.C8373, NewCertificates0261.C8374, NewCertificates0261.C8375, NewCertificates0261.C8376, NewCertificates0261.C8377, NewCertificates0261.C8378, NewCertificates0261.C8379} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0259.obstruction8308
  · exact NewCertificates0259.obstruction8309
  · exact NewCertificates0259.obstruction8310
  · exact NewCertificates0259.obstruction8311
  · exact NewCertificates0259.obstruction8312
  · exact NewCertificates0259.obstruction8313
  · exact NewCertificates0259.obstruction8314
  · exact NewCertificates0259.obstruction8315
  · exact NewCertificates0259.obstruction8316
  · exact NewCertificates0259.obstruction8317
  · exact NewCertificates0259.obstruction8318
  · exact NewCertificates0259.obstruction8319
  · exact NewCertificates0260.obstruction8320
  · exact NewCertificates0260.obstruction8321
  · exact NewCertificates0260.obstruction8322
  · exact NewCertificates0260.obstruction8323
  · exact NewCertificates0260.obstruction8324
  · exact NewCertificates0260.obstruction8325
  · exact NewCertificates0260.obstruction8326
  · exact NewCertificates0260.obstruction8327
  · exact NewCertificates0260.obstruction8328
  · exact NewCertificates0260.obstruction8329
  · exact NewCertificates0260.obstruction8330
  · exact NewCertificates0260.obstruction8331
  · exact NewCertificates0260.obstruction8332
  · exact NewCertificates0260.obstruction8333
  · exact NewCertificates0260.obstruction8334
  · exact NewCertificates0260.obstruction8335
  · exact NewCertificates0260.obstruction8336
  · exact NewCertificates0260.obstruction8337
  · exact NewCertificates0260.obstruction8338
  · exact NewCertificates0260.obstruction8339
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0260.obstruction8340
  · exact NewCertificates0260.obstruction8341
  · exact NewCertificates0260.obstruction8342
  · exact NewCertificates0260.obstruction8343
  · exact NewCertificates0260.obstruction8344
  · exact NewCertificates0260.obstruction8345
  · exact NewCertificates0260.obstruction8346
  · exact NewCertificates0260.obstruction8347
  · exact NewCertificates0260.obstruction8348
  · exact NewCertificates0260.obstruction8349
  · exact NewCertificates0260.obstruction8350
  · exact NewCertificates0260.obstruction8351
  · exact NewCertificates0261.obstruction8352
  · exact NewCertificates0261.obstruction8353
  · exact NewCertificates0261.obstruction8354
  · exact NewCertificates0261.obstruction8355
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0261.obstruction8356
  · exact NewCertificates0261.obstruction8357
  · exact NewCertificates0261.obstruction8358
  · exact NewCertificates0261.obstruction8359
  · exact NewCertificates0261.obstruction8360
  · exact NewCertificates0261.obstruction8361
  · exact NewCertificates0261.obstruction8362
  · exact NewCertificates0261.obstruction8363
  · exact NewCertificates0261.obstruction8364
  · exact NewCertificates0261.obstruction8365
  · exact NewCertificates0261.obstruction8366
  · exact NewCertificates0261.obstruction8367
  · exact NewCertificates0261.obstruction8368
  · exact NewCertificates0261.obstruction8369
  · exact NewCertificates0261.obstruction8370
  · exact NewCertificates0261.obstruction8371
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0261.obstruction8372
  · exact NewCertificates0261.obstruction8373
  · exact NewCertificates0261.obstruction8374
  · exact NewCertificates0261.obstruction8375
  · exact NewCertificates0261.obstruction8376
  · exact NewCertificates0261.obstruction8377
  · exact NewCertificates0261.obstruction8378
  · exact NewCertificates0261.obstruction8379
end Nut8.FiniteSupport178
