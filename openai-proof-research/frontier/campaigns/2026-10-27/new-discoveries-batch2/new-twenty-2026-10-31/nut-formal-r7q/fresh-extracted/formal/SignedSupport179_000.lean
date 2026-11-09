import SupportData179
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport179
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0261.C8380, NewCertificates0261.C8381, NewCertificates0261.C8382, NewCertificates0261.C8383, NewCertificates0262.C8384, NewCertificates0262.C8385, NewCertificates0262.C8386, NewCertificates0262.C8387, NewCertificates0262.C8388, NewCertificates0262.C8389, NewCertificates0262.C8390, NewCertificates0262.C8391, NewCertificates0262.C8392, NewCertificates0262.C8393, NewCertificates0262.C8394, NewCertificates0262.C8395} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0262.C8396, NewCertificates0262.C8397, NewCertificates0262.C8398, NewCertificates0262.C8399, NewCertificates0262.C8400, NewCertificates0262.C8401, NewCertificates0262.C8402, NewCertificates0262.C8403, NewCertificates0262.C8404, NewCertificates0262.C8405, NewCertificates0262.C8406, NewCertificates0262.C8407, NewCertificates0262.C8408, NewCertificates0262.C8409, NewCertificates0262.C8410, NewCertificates0262.C8411} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0262.C8412, NewCertificates0262.C8413, NewCertificates0262.C8414, NewCertificates0262.C8415, NewCertificates0263.C8416, NewCertificates0263.C8417, NewCertificates0263.C8418, NewCertificates0263.C8419, NewCertificates0263.C8420, NewCertificates0263.C8421, NewCertificates0263.C8422, NewCertificates0263.C8423, NewCertificates0263.C8424, NewCertificates0263.C8425, NewCertificates0263.C8426, NewCertificates0263.C8427} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0263.C8428, NewCertificates0263.C8429, NewCertificates0263.C8430, NewCertificates0263.C8431, NewCertificates0263.C8432, NewCertificates0263.C8433, NewCertificates0263.C8434, NewCertificates0263.C8435} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0261.obstruction8380
  · exact NewCertificates0261.obstruction8381
  · exact NewCertificates0261.obstruction8382
  · exact NewCertificates0261.obstruction8383
  · exact NewCertificates0262.obstruction8384
  · exact NewCertificates0262.obstruction8385
  · exact NewCertificates0262.obstruction8386
  · exact NewCertificates0262.obstruction8387
  · exact NewCertificates0262.obstruction8388
  · exact NewCertificates0262.obstruction8389
  · exact NewCertificates0262.obstruction8390
  · exact NewCertificates0262.obstruction8391
  · exact NewCertificates0262.obstruction8392
  · exact NewCertificates0262.obstruction8393
  · exact NewCertificates0262.obstruction8394
  · exact NewCertificates0262.obstruction8395
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0262.obstruction8396
  · exact NewCertificates0262.obstruction8397
  · exact NewCertificates0262.obstruction8398
  · exact NewCertificates0262.obstruction8399
  · exact NewCertificates0262.obstruction8400
  · exact NewCertificates0262.obstruction8401
  · exact NewCertificates0262.obstruction8402
  · exact NewCertificates0262.obstruction8403
  · exact NewCertificates0262.obstruction8404
  · exact NewCertificates0262.obstruction8405
  · exact NewCertificates0262.obstruction8406
  · exact NewCertificates0262.obstruction8407
  · exact NewCertificates0262.obstruction8408
  · exact NewCertificates0262.obstruction8409
  · exact NewCertificates0262.obstruction8410
  · exact NewCertificates0262.obstruction8411
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0262.obstruction8412
  · exact NewCertificates0262.obstruction8413
  · exact NewCertificates0262.obstruction8414
  · exact NewCertificates0262.obstruction8415
  · exact NewCertificates0263.obstruction8416
  · exact NewCertificates0263.obstruction8417
  · exact NewCertificates0263.obstruction8418
  · exact NewCertificates0263.obstruction8419
  · exact NewCertificates0263.obstruction8420
  · exact NewCertificates0263.obstruction8421
  · exact NewCertificates0263.obstruction8422
  · exact NewCertificates0263.obstruction8423
  · exact NewCertificates0263.obstruction8424
  · exact NewCertificates0263.obstruction8425
  · exact NewCertificates0263.obstruction8426
  · exact NewCertificates0263.obstruction8427
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0263.obstruction8428
  · exact NewCertificates0263.obstruction8429
  · exact NewCertificates0263.obstruction8430
  · exact NewCertificates0263.obstruction8431
  · exact NewCertificates0263.obstruction8432
  · exact NewCertificates0263.obstruction8433
  · exact NewCertificates0263.obstruction8434
  · exact NewCertificates0263.obstruction8435
end Nut8.FiniteSupport179
