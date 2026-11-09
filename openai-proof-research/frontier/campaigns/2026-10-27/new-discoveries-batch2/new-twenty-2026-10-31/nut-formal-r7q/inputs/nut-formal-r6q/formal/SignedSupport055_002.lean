import SupportData055
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport055
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0083.C2666, NewCertificates0083.C2667, NewCertificates0083.C2668, NewCertificates0083.C2669, NewCertificates0083.C2670, NewCertificates0083.C2671, NewCertificates0083.C2672, NewCertificates0083.C2673} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0083.C2674, NewCertificates0083.C2675, NewCertificates0083.C2676, NewCertificates0083.C2677, NewCertificates0083.C2678, NewCertificates0083.C2679, NewCertificates0083.C2680, NewCertificates0083.C2681} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0083.C2682, NewCertificates0083.C2683, NewCertificates0083.C2684, NewCertificates0083.C2685, NewCertificates0083.C2686, NewCertificates0083.C2687, NewCertificates0084.C2688, NewCertificates0084.C2689} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0084.C2690, NewCertificates0084.C2691, NewCertificates0084.C2692, NewCertificates0084.C2693, NewCertificates0084.C2694, NewCertificates0084.C2695, NewCertificates0084.C2696, NewCertificates0084.C2697} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0083.obstruction2666
  · exact NewCertificates0083.obstruction2667
  · exact NewCertificates0083.obstruction2668
  · exact NewCertificates0083.obstruction2669
  · exact NewCertificates0083.obstruction2670
  · exact NewCertificates0083.obstruction2671
  · exact NewCertificates0083.obstruction2672
  · exact NewCertificates0083.obstruction2673
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0083.obstruction2674
  · exact NewCertificates0083.obstruction2675
  · exact NewCertificates0083.obstruction2676
  · exact NewCertificates0083.obstruction2677
  · exact NewCertificates0083.obstruction2678
  · exact NewCertificates0083.obstruction2679
  · exact NewCertificates0083.obstruction2680
  · exact NewCertificates0083.obstruction2681
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0083.obstruction2682
  · exact NewCertificates0083.obstruction2683
  · exact NewCertificates0083.obstruction2684
  · exact NewCertificates0083.obstruction2685
  · exact NewCertificates0083.obstruction2686
  · exact NewCertificates0083.obstruction2687
  · exact NewCertificates0084.obstruction2688
  · exact NewCertificates0084.obstruction2689
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0084.obstruction2690
  · exact NewCertificates0084.obstruction2691
  · exact NewCertificates0084.obstruction2692
  · exact NewCertificates0084.obstruction2693
  · exact NewCertificates0084.obstruction2694
  · exact NewCertificates0084.obstruction2695
  · exact NewCertificates0084.obstruction2696
  · exact NewCertificates0084.obstruction2697
end Nut8.FiniteSupport055
