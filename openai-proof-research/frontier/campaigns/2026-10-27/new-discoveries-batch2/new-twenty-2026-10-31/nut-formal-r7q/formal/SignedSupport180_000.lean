import SupportData180
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport180
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0263.C8436, NewCertificates0263.C8437, NewCertificates0263.C8438, NewCertificates0263.C8439, NewCertificates0263.C8440, NewCertificates0263.C8441, NewCertificates0263.C8442, NewCertificates0263.C8443, NewCertificates0263.C8444, NewCertificates0263.C8445, NewCertificates0263.C8446, NewCertificates0263.C8447, NewCertificates0264.C8448, NewCertificates0264.C8449, NewCertificates0264.C8450, NewCertificates0264.C8451} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0264.C8452, NewCertificates0264.C8453, NewCertificates0264.C8454, NewCertificates0264.C8455, NewCertificates0264.C8456, NewCertificates0264.C8457, NewCertificates0264.C8458, NewCertificates0264.C8459, NewCertificates0264.C8460, NewCertificates0264.C8461, NewCertificates0264.C8462, NewCertificates0264.C8463, NewCertificates0264.C8464, NewCertificates0264.C8465, NewCertificates0264.C8466, NewCertificates0264.C8467} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0264.C8468, NewCertificates0264.C8469, NewCertificates0264.C8470, NewCertificates0264.C8471, NewCertificates0264.C8472, NewCertificates0264.C8473, NewCertificates0264.C8474, NewCertificates0264.C8475, NewCertificates0264.C8476, NewCertificates0264.C8477, NewCertificates0264.C8478, NewCertificates0264.C8479, NewCertificates0265.C8480, NewCertificates0265.C8481, NewCertificates0265.C8482, NewCertificates0265.C8483} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0265.C8484, NewCertificates0265.C8485, NewCertificates0265.C8486, NewCertificates0265.C8487, NewCertificates0265.C8488, NewCertificates0265.C8489, NewCertificates0265.C8490, NewCertificates0265.C8491} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0263.obstruction8436
  · exact NewCertificates0263.obstruction8437
  · exact NewCertificates0263.obstruction8438
  · exact NewCertificates0263.obstruction8439
  · exact NewCertificates0263.obstruction8440
  · exact NewCertificates0263.obstruction8441
  · exact NewCertificates0263.obstruction8442
  · exact NewCertificates0263.obstruction8443
  · exact NewCertificates0263.obstruction8444
  · exact NewCertificates0263.obstruction8445
  · exact NewCertificates0263.obstruction8446
  · exact NewCertificates0263.obstruction8447
  · exact NewCertificates0264.obstruction8448
  · exact NewCertificates0264.obstruction8449
  · exact NewCertificates0264.obstruction8450
  · exact NewCertificates0264.obstruction8451
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0264.obstruction8452
  · exact NewCertificates0264.obstruction8453
  · exact NewCertificates0264.obstruction8454
  · exact NewCertificates0264.obstruction8455
  · exact NewCertificates0264.obstruction8456
  · exact NewCertificates0264.obstruction8457
  · exact NewCertificates0264.obstruction8458
  · exact NewCertificates0264.obstruction8459
  · exact NewCertificates0264.obstruction8460
  · exact NewCertificates0264.obstruction8461
  · exact NewCertificates0264.obstruction8462
  · exact NewCertificates0264.obstruction8463
  · exact NewCertificates0264.obstruction8464
  · exact NewCertificates0264.obstruction8465
  · exact NewCertificates0264.obstruction8466
  · exact NewCertificates0264.obstruction8467
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0264.obstruction8468
  · exact NewCertificates0264.obstruction8469
  · exact NewCertificates0264.obstruction8470
  · exact NewCertificates0264.obstruction8471
  · exact NewCertificates0264.obstruction8472
  · exact NewCertificates0264.obstruction8473
  · exact NewCertificates0264.obstruction8474
  · exact NewCertificates0264.obstruction8475
  · exact NewCertificates0264.obstruction8476
  · exact NewCertificates0264.obstruction8477
  · exact NewCertificates0264.obstruction8478
  · exact NewCertificates0264.obstruction8479
  · exact NewCertificates0265.obstruction8480
  · exact NewCertificates0265.obstruction8481
  · exact NewCertificates0265.obstruction8482
  · exact NewCertificates0265.obstruction8483
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0265.obstruction8484
  · exact NewCertificates0265.obstruction8485
  · exact NewCertificates0265.obstruction8486
  · exact NewCertificates0265.obstruction8487
  · exact NewCertificates0265.obstruction8488
  · exact NewCertificates0265.obstruction8489
  · exact NewCertificates0265.obstruction8490
  · exact NewCertificates0265.obstruction8491
end Nut8.FiniteSupport180
