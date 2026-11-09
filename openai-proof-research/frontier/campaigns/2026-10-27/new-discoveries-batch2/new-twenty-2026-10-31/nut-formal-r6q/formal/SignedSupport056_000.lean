import SupportData056
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport056
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0084.C2702, NewCertificates0084.C2703, NewCertificates0084.C2704, NewCertificates0084.C2705, NewCertificates0084.C2706, NewCertificates0084.C2707, NewCertificates0084.C2708, NewCertificates0084.C2709, NewCertificates0084.C2710, NewCertificates0084.C2711, NewCertificates0084.C2712, NewCertificates0084.C2713, NewCertificates0084.C2714, NewCertificates0084.C2715, NewCertificates0084.C2716, NewCertificates0084.C2717} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0084.C2718, NewCertificates0084.C2719, NewCertificates0085.C2720, NewCertificates0085.C2721, NewCertificates0085.C2722, NewCertificates0085.C2723, NewCertificates0085.C2724, NewCertificates0085.C2725, NewCertificates0085.C2726, NewCertificates0085.C2727, NewCertificates0085.C2728, NewCertificates0085.C2729, NewCertificates0085.C2730, NewCertificates0085.C2731, NewCertificates0085.C2732, NewCertificates0085.C2733} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0084.obstruction2702
  · exact NewCertificates0084.obstruction2703
  · exact NewCertificates0084.obstruction2704
  · exact NewCertificates0084.obstruction2705
  · exact NewCertificates0084.obstruction2706
  · exact NewCertificates0084.obstruction2707
  · exact NewCertificates0084.obstruction2708
  · exact NewCertificates0084.obstruction2709
  · exact NewCertificates0084.obstruction2710
  · exact NewCertificates0084.obstruction2711
  · exact NewCertificates0084.obstruction2712
  · exact NewCertificates0084.obstruction2713
  · exact NewCertificates0084.obstruction2714
  · exact NewCertificates0084.obstruction2715
  · exact NewCertificates0084.obstruction2716
  · exact NewCertificates0084.obstruction2717
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0084.obstruction2718
  · exact NewCertificates0084.obstruction2719
  · exact NewCertificates0085.obstruction2720
  · exact NewCertificates0085.obstruction2721
  · exact NewCertificates0085.obstruction2722
  · exact NewCertificates0085.obstruction2723
  · exact NewCertificates0085.obstruction2724
  · exact NewCertificates0085.obstruction2725
  · exact NewCertificates0085.obstruction2726
  · exact NewCertificates0085.obstruction2727
  · exact NewCertificates0085.obstruction2728
  · exact NewCertificates0085.obstruction2729
  · exact NewCertificates0085.obstruction2730
  · exact NewCertificates0085.obstruction2731
  · exact NewCertificates0085.obstruction2732
  · exact NewCertificates0085.obstruction2733
end Nut8.FiniteSupport056
