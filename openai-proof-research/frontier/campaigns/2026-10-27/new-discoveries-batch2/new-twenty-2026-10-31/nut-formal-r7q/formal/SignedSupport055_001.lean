import SupportData055
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport055
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0082.C2634, NewCertificates0082.C2635, NewCertificates0082.C2636, NewCertificates0082.C2637, NewCertificates0082.C2638, NewCertificates0082.C2639, NewCertificates0082.C2640, NewCertificates0082.C2641} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0082.C2642, NewCertificates0082.C2643, NewCertificates0082.C2644, NewCertificates0082.C2645, NewCertificates0082.C2646, NewCertificates0082.C2647, NewCertificates0082.C2648, NewCertificates0082.C2649} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0082.C2650, NewCertificates0082.C2651, NewCertificates0082.C2652, NewCertificates0082.C2653, NewCertificates0082.C2654, NewCertificates0082.C2655, NewCertificates0083.C2656, NewCertificates0083.C2657} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0083.C2658, NewCertificates0083.C2659, NewCertificates0083.C2660, NewCertificates0083.C2661, NewCertificates0083.C2662, NewCertificates0083.C2663, NewCertificates0083.C2664, NewCertificates0083.C2665} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0082.obstruction2634
  · exact NewCertificates0082.obstruction2635
  · exact NewCertificates0082.obstruction2636
  · exact NewCertificates0082.obstruction2637
  · exact NewCertificates0082.obstruction2638
  · exact NewCertificates0082.obstruction2639
  · exact NewCertificates0082.obstruction2640
  · exact NewCertificates0082.obstruction2641
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0082.obstruction2642
  · exact NewCertificates0082.obstruction2643
  · exact NewCertificates0082.obstruction2644
  · exact NewCertificates0082.obstruction2645
  · exact NewCertificates0082.obstruction2646
  · exact NewCertificates0082.obstruction2647
  · exact NewCertificates0082.obstruction2648
  · exact NewCertificates0082.obstruction2649
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0082.obstruction2650
  · exact NewCertificates0082.obstruction2651
  · exact NewCertificates0082.obstruction2652
  · exact NewCertificates0082.obstruction2653
  · exact NewCertificates0082.obstruction2654
  · exact NewCertificates0082.obstruction2655
  · exact NewCertificates0083.obstruction2656
  · exact NewCertificates0083.obstruction2657
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0083.obstruction2658
  · exact NewCertificates0083.obstruction2659
  · exact NewCertificates0083.obstruction2660
  · exact NewCertificates0083.obstruction2661
  · exact NewCertificates0083.obstruction2662
  · exact NewCertificates0083.obstruction2663
  · exact NewCertificates0083.obstruction2664
  · exact NewCertificates0083.obstruction2665
end Nut8.FiniteSupport055
