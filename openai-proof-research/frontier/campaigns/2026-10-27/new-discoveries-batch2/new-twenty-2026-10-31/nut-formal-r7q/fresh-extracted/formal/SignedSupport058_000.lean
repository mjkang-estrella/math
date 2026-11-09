import SupportData058
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport058
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0086.C2766, NewCertificates0086.C2767, NewCertificates0086.C2768, NewCertificates0086.C2769, NewCertificates0086.C2770, NewCertificates0086.C2771, NewCertificates0086.C2772, NewCertificates0086.C2773, NewCertificates0086.C2774, NewCertificates0086.C2775, NewCertificates0086.C2776, NewCertificates0086.C2777, NewCertificates0086.C2778, NewCertificates0086.C2779, NewCertificates0086.C2780, NewCertificates0086.C2781} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0086.C2782, NewCertificates0086.C2783, NewCertificates0087.C2784, NewCertificates0087.C2785, NewCertificates0087.C2786, NewCertificates0087.C2787, NewCertificates0087.C2788, NewCertificates0087.C2789, NewCertificates0087.C2790, NewCertificates0087.C2791, NewCertificates0087.C2792, NewCertificates0087.C2793, NewCertificates0087.C2794, NewCertificates0087.C2795, NewCertificates0087.C2796, NewCertificates0087.C2797} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0086.obstruction2766
  · exact NewCertificates0086.obstruction2767
  · exact NewCertificates0086.obstruction2768
  · exact NewCertificates0086.obstruction2769
  · exact NewCertificates0086.obstruction2770
  · exact NewCertificates0086.obstruction2771
  · exact NewCertificates0086.obstruction2772
  · exact NewCertificates0086.obstruction2773
  · exact NewCertificates0086.obstruction2774
  · exact NewCertificates0086.obstruction2775
  · exact NewCertificates0086.obstruction2776
  · exact NewCertificates0086.obstruction2777
  · exact NewCertificates0086.obstruction2778
  · exact NewCertificates0086.obstruction2779
  · exact NewCertificates0086.obstruction2780
  · exact NewCertificates0086.obstruction2781
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0086.obstruction2782
  · exact NewCertificates0086.obstruction2783
  · exact NewCertificates0087.obstruction2784
  · exact NewCertificates0087.obstruction2785
  · exact NewCertificates0087.obstruction2786
  · exact NewCertificates0087.obstruction2787
  · exact NewCertificates0087.obstruction2788
  · exact NewCertificates0087.obstruction2789
  · exact NewCertificates0087.obstruction2790
  · exact NewCertificates0087.obstruction2791
  · exact NewCertificates0087.obstruction2792
  · exact NewCertificates0087.obstruction2793
  · exact NewCertificates0087.obstruction2794
  · exact NewCertificates0087.obstruction2795
  · exact NewCertificates0087.obstruction2796
  · exact NewCertificates0087.obstruction2797
end Nut8.FiniteSupport058
