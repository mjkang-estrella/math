import SupportData055
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport055
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0081.C2602, NewCertificates0081.C2603, NewCertificates0081.C2604, NewCertificates0081.C2605, NewCertificates0081.C2606, NewCertificates0081.C2607, NewCertificates0081.C2608, NewCertificates0081.C2609} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0081.C2610, NewCertificates0081.C2611, NewCertificates0081.C2612, NewCertificates0081.C2613, NewCertificates0081.C2614, NewCertificates0081.C2615, NewCertificates0081.C2616, NewCertificates0081.C2617} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0081.C2618, NewCertificates0081.C2619, NewCertificates0081.C2620, NewCertificates0081.C2621, NewCertificates0081.C2622, NewCertificates0081.C2623, NewCertificates0082.C2624, NewCertificates0082.C2625} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0082.C2626, NewCertificates0082.C2627, NewCertificates0082.C2628, NewCertificates0082.C2629, NewCertificates0082.C2630, NewCertificates0082.C2631, NewCertificates0082.C2632, NewCertificates0082.C2633} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0081.obstruction2602
  · exact NewCertificates0081.obstruction2603
  · exact NewCertificates0081.obstruction2604
  · exact NewCertificates0081.obstruction2605
  · exact NewCertificates0081.obstruction2606
  · exact NewCertificates0081.obstruction2607
  · exact NewCertificates0081.obstruction2608
  · exact NewCertificates0081.obstruction2609
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0081.obstruction2610
  · exact NewCertificates0081.obstruction2611
  · exact NewCertificates0081.obstruction2612
  · exact NewCertificates0081.obstruction2613
  · exact NewCertificates0081.obstruction2614
  · exact NewCertificates0081.obstruction2615
  · exact NewCertificates0081.obstruction2616
  · exact NewCertificates0081.obstruction2617
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0081.obstruction2618
  · exact NewCertificates0081.obstruction2619
  · exact NewCertificates0081.obstruction2620
  · exact NewCertificates0081.obstruction2621
  · exact NewCertificates0081.obstruction2622
  · exact NewCertificates0081.obstruction2623
  · exact NewCertificates0082.obstruction2624
  · exact NewCertificates0082.obstruction2625
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0082.obstruction2626
  · exact NewCertificates0082.obstruction2627
  · exact NewCertificates0082.obstruction2628
  · exact NewCertificates0082.obstruction2629
  · exact NewCertificates0082.obstruction2630
  · exact NewCertificates0082.obstruction2631
  · exact NewCertificates0082.obstruction2632
  · exact NewCertificates0082.obstruction2633
end Nut8.FiniteSupport055
