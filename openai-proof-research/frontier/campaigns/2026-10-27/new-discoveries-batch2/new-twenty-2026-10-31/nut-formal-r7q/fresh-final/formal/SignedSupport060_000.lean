import SupportData060
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport060
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0088.C2830, NewCertificates0088.C2831, NewCertificates0088.C2832, NewCertificates0088.C2833, NewCertificates0088.C2834, NewCertificates0088.C2835, NewCertificates0088.C2836, NewCertificates0088.C2837, NewCertificates0088.C2838, NewCertificates0088.C2839, NewCertificates0088.C2840, NewCertificates0088.C2841, NewCertificates0088.C2842, NewCertificates0088.C2843, NewCertificates0088.C2844, NewCertificates0088.C2845, NewCertificates0088.C2846, NewCertificates0088.C2847, NewCertificates0089.C2848, NewCertificates0089.C2849, NewCertificates0089.C2850, NewCertificates0089.C2851, NewCertificates0089.C2852, NewCertificates0089.C2853, NewCertificates0089.C2854, NewCertificates0089.C2855, NewCertificates0089.C2856, NewCertificates0089.C2857, NewCertificates0089.C2858, NewCertificates0089.C2859, NewCertificates0089.C2860, NewCertificates0089.C2861} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0088.obstruction2830
  · exact NewCertificates0088.obstruction2831
  · exact NewCertificates0088.obstruction2832
  · exact NewCertificates0088.obstruction2833
  · exact NewCertificates0088.obstruction2834
  · exact NewCertificates0088.obstruction2835
  · exact NewCertificates0088.obstruction2836
  · exact NewCertificates0088.obstruction2837
  · exact NewCertificates0088.obstruction2838
  · exact NewCertificates0088.obstruction2839
  · exact NewCertificates0088.obstruction2840
  · exact NewCertificates0088.obstruction2841
  · exact NewCertificates0088.obstruction2842
  · exact NewCertificates0088.obstruction2843
  · exact NewCertificates0088.obstruction2844
  · exact NewCertificates0088.obstruction2845
  · exact NewCertificates0088.obstruction2846
  · exact NewCertificates0088.obstruction2847
  · exact NewCertificates0089.obstruction2848
  · exact NewCertificates0089.obstruction2849
  · exact NewCertificates0089.obstruction2850
  · exact NewCertificates0089.obstruction2851
  · exact NewCertificates0089.obstruction2852
  · exact NewCertificates0089.obstruction2853
  · exact NewCertificates0089.obstruction2854
  · exact NewCertificates0089.obstruction2855
  · exact NewCertificates0089.obstruction2856
  · exact NewCertificates0089.obstruction2857
  · exact NewCertificates0089.obstruction2858
  · exact NewCertificates0089.obstruction2859
  · exact NewCertificates0089.obstruction2860
  · exact NewCertificates0089.obstruction2861
end Nut8.FiniteSupport060
