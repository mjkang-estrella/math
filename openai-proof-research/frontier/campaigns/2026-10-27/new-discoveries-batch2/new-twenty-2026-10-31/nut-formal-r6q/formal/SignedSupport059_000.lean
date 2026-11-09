import SupportData059
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport059
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0087.C2798, NewCertificates0087.C2799, NewCertificates0087.C2800, NewCertificates0087.C2801, NewCertificates0087.C2802, NewCertificates0087.C2803, NewCertificates0087.C2804, NewCertificates0087.C2805, NewCertificates0087.C2806, NewCertificates0087.C2807, NewCertificates0087.C2808, NewCertificates0087.C2809, NewCertificates0087.C2810, NewCertificates0087.C2811, NewCertificates0087.C2812, NewCertificates0087.C2813} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0087.C2814, NewCertificates0087.C2815, NewCertificates0088.C2816, NewCertificates0088.C2817, NewCertificates0088.C2818, NewCertificates0088.C2819, NewCertificates0088.C2820, NewCertificates0088.C2821, NewCertificates0088.C2822, NewCertificates0088.C2823, NewCertificates0088.C2824, NewCertificates0088.C2825, NewCertificates0088.C2826, NewCertificates0088.C2827, NewCertificates0088.C2828, NewCertificates0088.C2829} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0087.obstruction2798
  · exact NewCertificates0087.obstruction2799
  · exact NewCertificates0087.obstruction2800
  · exact NewCertificates0087.obstruction2801
  · exact NewCertificates0087.obstruction2802
  · exact NewCertificates0087.obstruction2803
  · exact NewCertificates0087.obstruction2804
  · exact NewCertificates0087.obstruction2805
  · exact NewCertificates0087.obstruction2806
  · exact NewCertificates0087.obstruction2807
  · exact NewCertificates0087.obstruction2808
  · exact NewCertificates0087.obstruction2809
  · exact NewCertificates0087.obstruction2810
  · exact NewCertificates0087.obstruction2811
  · exact NewCertificates0087.obstruction2812
  · exact NewCertificates0087.obstruction2813
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0087.obstruction2814
  · exact NewCertificates0087.obstruction2815
  · exact NewCertificates0088.obstruction2816
  · exact NewCertificates0088.obstruction2817
  · exact NewCertificates0088.obstruction2818
  · exact NewCertificates0088.obstruction2819
  · exact NewCertificates0088.obstruction2820
  · exact NewCertificates0088.obstruction2821
  · exact NewCertificates0088.obstruction2822
  · exact NewCertificates0088.obstruction2823
  · exact NewCertificates0088.obstruction2824
  · exact NewCertificates0088.obstruction2825
  · exact NewCertificates0088.obstruction2826
  · exact NewCertificates0088.obstruction2827
  · exact NewCertificates0088.obstruction2828
  · exact NewCertificates0088.obstruction2829
end Nut8.FiniteSupport059
