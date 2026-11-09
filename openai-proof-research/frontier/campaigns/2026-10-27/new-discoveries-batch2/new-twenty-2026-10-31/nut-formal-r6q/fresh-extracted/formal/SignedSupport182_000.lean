import SupportData182
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport182
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0267.C8548, NewCertificates0267.C8549, NewCertificates0267.C8550, NewCertificates0267.C8551, NewCertificates0267.C8552, NewCertificates0267.C8553, NewCertificates0267.C8554, NewCertificates0267.C8555, NewCertificates0267.C8556, NewCertificates0267.C8557, NewCertificates0267.C8558, NewCertificates0267.C8559, NewCertificates0267.C8560, NewCertificates0267.C8561, NewCertificates0267.C8562, NewCertificates0267.C8563} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0267.C8564, NewCertificates0267.C8565, NewCertificates0267.C8566, NewCertificates0267.C8567, NewCertificates0267.C8568, NewCertificates0267.C8569, NewCertificates0267.C8570, NewCertificates0267.C8571, NewCertificates0267.C8572, NewCertificates0267.C8573, NewCertificates0267.C8574, NewCertificates0267.C8575, NewCertificates0268.C8576, NewCertificates0268.C8577, NewCertificates0268.C8578, NewCertificates0268.C8579} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0268.C8580, NewCertificates0268.C8581, NewCertificates0268.C8582, NewCertificates0268.C8583, NewCertificates0268.C8584, NewCertificates0268.C8585, NewCertificates0268.C8586, NewCertificates0268.C8587, NewCertificates0268.C8588, NewCertificates0268.C8589, NewCertificates0268.C8590, NewCertificates0268.C8591, NewCertificates0268.C8592, NewCertificates0268.C8593, NewCertificates0268.C8594, NewCertificates0268.C8595} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0268.C8596, NewCertificates0268.C8597, NewCertificates0268.C8598, NewCertificates0268.C8599, NewCertificates0268.C8600, NewCertificates0268.C8601, NewCertificates0268.C8602, NewCertificates0268.C8603, NewCertificates0268.C8604, NewCertificates0268.C8605, NewCertificates0268.C8606, NewCertificates0268.C8607, NewCertificates0269.C8608, NewCertificates0269.C8609, NewCertificates0269.C8610, NewCertificates0269.C8611} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0267.obstruction8548
  · exact NewCertificates0267.obstruction8549
  · exact NewCertificates0267.obstruction8550
  · exact NewCertificates0267.obstruction8551
  · exact NewCertificates0267.obstruction8552
  · exact NewCertificates0267.obstruction8553
  · exact NewCertificates0267.obstruction8554
  · exact NewCertificates0267.obstruction8555
  · exact NewCertificates0267.obstruction8556
  · exact NewCertificates0267.obstruction8557
  · exact NewCertificates0267.obstruction8558
  · exact NewCertificates0267.obstruction8559
  · exact NewCertificates0267.obstruction8560
  · exact NewCertificates0267.obstruction8561
  · exact NewCertificates0267.obstruction8562
  · exact NewCertificates0267.obstruction8563
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0267.obstruction8564
  · exact NewCertificates0267.obstruction8565
  · exact NewCertificates0267.obstruction8566
  · exact NewCertificates0267.obstruction8567
  · exact NewCertificates0267.obstruction8568
  · exact NewCertificates0267.obstruction8569
  · exact NewCertificates0267.obstruction8570
  · exact NewCertificates0267.obstruction8571
  · exact NewCertificates0267.obstruction8572
  · exact NewCertificates0267.obstruction8573
  · exact NewCertificates0267.obstruction8574
  · exact NewCertificates0267.obstruction8575
  · exact NewCertificates0268.obstruction8576
  · exact NewCertificates0268.obstruction8577
  · exact NewCertificates0268.obstruction8578
  · exact NewCertificates0268.obstruction8579
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0268.obstruction8580
  · exact NewCertificates0268.obstruction8581
  · exact NewCertificates0268.obstruction8582
  · exact NewCertificates0268.obstruction8583
  · exact NewCertificates0268.obstruction8584
  · exact NewCertificates0268.obstruction8585
  · exact NewCertificates0268.obstruction8586
  · exact NewCertificates0268.obstruction8587
  · exact NewCertificates0268.obstruction8588
  · exact NewCertificates0268.obstruction8589
  · exact NewCertificates0268.obstruction8590
  · exact NewCertificates0268.obstruction8591
  · exact NewCertificates0268.obstruction8592
  · exact NewCertificates0268.obstruction8593
  · exact NewCertificates0268.obstruction8594
  · exact NewCertificates0268.obstruction8595
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0268.obstruction8596
  · exact NewCertificates0268.obstruction8597
  · exact NewCertificates0268.obstruction8598
  · exact NewCertificates0268.obstruction8599
  · exact NewCertificates0268.obstruction8600
  · exact NewCertificates0268.obstruction8601
  · exact NewCertificates0268.obstruction8602
  · exact NewCertificates0268.obstruction8603
  · exact NewCertificates0268.obstruction8604
  · exact NewCertificates0268.obstruction8605
  · exact NewCertificates0268.obstruction8606
  · exact NewCertificates0268.obstruction8607
  · exact NewCertificates0269.obstruction8608
  · exact NewCertificates0269.obstruction8609
  · exact NewCertificates0269.obstruction8610
  · exact NewCertificates0269.obstruction8611
end Nut8.FiniteSupport182
