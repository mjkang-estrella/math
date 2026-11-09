import SupportData183
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport183
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0269.C8620, NewCertificates0269.C8621, NewCertificates0269.C8622, NewCertificates0269.C8623, NewCertificates0269.C8624, NewCertificates0269.C8625, NewCertificates0269.C8626, NewCertificates0269.C8627, NewCertificates0269.C8628, NewCertificates0269.C8629, NewCertificates0269.C8630, NewCertificates0269.C8631, NewCertificates0269.C8632, NewCertificates0269.C8633, NewCertificates0269.C8634, NewCertificates0269.C8635, NewCertificates0269.C8636, NewCertificates0269.C8637, NewCertificates0269.C8638, NewCertificates0269.C8639, NewCertificates0270.C8640, NewCertificates0270.C8641, NewCertificates0270.C8642, NewCertificates0270.C8643, NewCertificates0270.C8644, NewCertificates0270.C8645, NewCertificates0270.C8646, NewCertificates0270.C8647, NewCertificates0270.C8648, NewCertificates0270.C8649, NewCertificates0270.C8650, NewCertificates0270.C8651} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0270.C8652, NewCertificates0270.C8653, NewCertificates0270.C8654, NewCertificates0270.C8655, NewCertificates0270.C8656, NewCertificates0270.C8657, NewCertificates0270.C8658, NewCertificates0270.C8659, NewCertificates0270.C8660, NewCertificates0270.C8661, NewCertificates0270.C8662, NewCertificates0270.C8663, NewCertificates0270.C8664, NewCertificates0270.C8665, NewCertificates0270.C8666, NewCertificates0270.C8667} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0269.obstruction8620
  · exact NewCertificates0269.obstruction8621
  · exact NewCertificates0269.obstruction8622
  · exact NewCertificates0269.obstruction8623
  · exact NewCertificates0269.obstruction8624
  · exact NewCertificates0269.obstruction8625
  · exact NewCertificates0269.obstruction8626
  · exact NewCertificates0269.obstruction8627
  · exact NewCertificates0269.obstruction8628
  · exact NewCertificates0269.obstruction8629
  · exact NewCertificates0269.obstruction8630
  · exact NewCertificates0269.obstruction8631
  · exact NewCertificates0269.obstruction8632
  · exact NewCertificates0269.obstruction8633
  · exact NewCertificates0269.obstruction8634
  · exact NewCertificates0269.obstruction8635
  · exact NewCertificates0269.obstruction8636
  · exact NewCertificates0269.obstruction8637
  · exact NewCertificates0269.obstruction8638
  · exact NewCertificates0269.obstruction8639
  · exact NewCertificates0270.obstruction8640
  · exact NewCertificates0270.obstruction8641
  · exact NewCertificates0270.obstruction8642
  · exact NewCertificates0270.obstruction8643
  · exact NewCertificates0270.obstruction8644
  · exact NewCertificates0270.obstruction8645
  · exact NewCertificates0270.obstruction8646
  · exact NewCertificates0270.obstruction8647
  · exact NewCertificates0270.obstruction8648
  · exact NewCertificates0270.obstruction8649
  · exact NewCertificates0270.obstruction8650
  · exact NewCertificates0270.obstruction8651
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0270.obstruction8652
  · exact NewCertificates0270.obstruction8653
  · exact NewCertificates0270.obstruction8654
  · exact NewCertificates0270.obstruction8655
  · exact NewCertificates0270.obstruction8656
  · exact NewCertificates0270.obstruction8657
  · exact NewCertificates0270.obstruction8658
  · exact NewCertificates0270.obstruction8659
  · exact NewCertificates0270.obstruction8660
  · exact NewCertificates0270.obstruction8661
  · exact NewCertificates0270.obstruction8662
  · exact NewCertificates0270.obstruction8663
  · exact NewCertificates0270.obstruction8664
  · exact NewCertificates0270.obstruction8665
  · exact NewCertificates0270.obstruction8666
  · exact NewCertificates0270.obstruction8667
end Nut8.FiniteSupport183
