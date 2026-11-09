import SupportData181
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport181
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0265.C8492, NewCertificates0265.C8493, NewCertificates0265.C8494, NewCertificates0265.C8495, NewCertificates0265.C8496, NewCertificates0265.C8497, NewCertificates0265.C8498, NewCertificates0265.C8499, NewCertificates0265.C8500, NewCertificates0265.C8501, NewCertificates0265.C8502, NewCertificates0265.C8503, NewCertificates0265.C8504, NewCertificates0265.C8505, NewCertificates0265.C8506, NewCertificates0265.C8507} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0265.C8508, NewCertificates0265.C8509, NewCertificates0265.C8510, NewCertificates0265.C8511, NewCertificates0266.C8512, NewCertificates0266.C8513, NewCertificates0266.C8514, NewCertificates0266.C8515, NewCertificates0266.C8516, NewCertificates0266.C8517, NewCertificates0266.C8518, NewCertificates0266.C8519, NewCertificates0266.C8520, NewCertificates0266.C8521, NewCertificates0266.C8522, NewCertificates0266.C8523} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0266.C8524, NewCertificates0266.C8525, NewCertificates0266.C8526, NewCertificates0266.C8527, NewCertificates0266.C8528, NewCertificates0266.C8529, NewCertificates0266.C8530, NewCertificates0266.C8531, NewCertificates0266.C8532, NewCertificates0266.C8533, NewCertificates0266.C8534, NewCertificates0266.C8535, NewCertificates0266.C8536, NewCertificates0266.C8537, NewCertificates0266.C8538, NewCertificates0266.C8539} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0266.C8540, NewCertificates0266.C8541, NewCertificates0266.C8542, NewCertificates0266.C8543, NewCertificates0267.C8544, NewCertificates0267.C8545, NewCertificates0267.C8546, NewCertificates0267.C8547} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0265.obstruction8492
  · exact NewCertificates0265.obstruction8493
  · exact NewCertificates0265.obstruction8494
  · exact NewCertificates0265.obstruction8495
  · exact NewCertificates0265.obstruction8496
  · exact NewCertificates0265.obstruction8497
  · exact NewCertificates0265.obstruction8498
  · exact NewCertificates0265.obstruction8499
  · exact NewCertificates0265.obstruction8500
  · exact NewCertificates0265.obstruction8501
  · exact NewCertificates0265.obstruction8502
  · exact NewCertificates0265.obstruction8503
  · exact NewCertificates0265.obstruction8504
  · exact NewCertificates0265.obstruction8505
  · exact NewCertificates0265.obstruction8506
  · exact NewCertificates0265.obstruction8507
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0265.obstruction8508
  · exact NewCertificates0265.obstruction8509
  · exact NewCertificates0265.obstruction8510
  · exact NewCertificates0265.obstruction8511
  · exact NewCertificates0266.obstruction8512
  · exact NewCertificates0266.obstruction8513
  · exact NewCertificates0266.obstruction8514
  · exact NewCertificates0266.obstruction8515
  · exact NewCertificates0266.obstruction8516
  · exact NewCertificates0266.obstruction8517
  · exact NewCertificates0266.obstruction8518
  · exact NewCertificates0266.obstruction8519
  · exact NewCertificates0266.obstruction8520
  · exact NewCertificates0266.obstruction8521
  · exact NewCertificates0266.obstruction8522
  · exact NewCertificates0266.obstruction8523
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0266.obstruction8524
  · exact NewCertificates0266.obstruction8525
  · exact NewCertificates0266.obstruction8526
  · exact NewCertificates0266.obstruction8527
  · exact NewCertificates0266.obstruction8528
  · exact NewCertificates0266.obstruction8529
  · exact NewCertificates0266.obstruction8530
  · exact NewCertificates0266.obstruction8531
  · exact NewCertificates0266.obstruction8532
  · exact NewCertificates0266.obstruction8533
  · exact NewCertificates0266.obstruction8534
  · exact NewCertificates0266.obstruction8535
  · exact NewCertificates0266.obstruction8536
  · exact NewCertificates0266.obstruction8537
  · exact NewCertificates0266.obstruction8538
  · exact NewCertificates0266.obstruction8539
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0266.obstruction8540
  · exact NewCertificates0266.obstruction8541
  · exact NewCertificates0266.obstruction8542
  · exact NewCertificates0266.obstruction8543
  · exact NewCertificates0267.obstruction8544
  · exact NewCertificates0267.obstruction8545
  · exact NewCertificates0267.obstruction8546
  · exact NewCertificates0267.obstruction8547
end Nut8.FiniteSupport181
