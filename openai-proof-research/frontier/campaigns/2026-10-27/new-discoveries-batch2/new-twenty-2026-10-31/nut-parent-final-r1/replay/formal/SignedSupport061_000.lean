import SupportData061
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport061
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0089.C2862, NewCertificates0089.C2863, NewCertificates0089.C2864, NewCertificates0089.C2865, NewCertificates0089.C2866, NewCertificates0089.C2867, NewCertificates0089.C2868, NewCertificates0089.C2869, NewCertificates0089.C2870, NewCertificates0089.C2871, NewCertificates0089.C2872, NewCertificates0089.C2873, NewCertificates0089.C2874, NewCertificates0089.C2875, NewCertificates0089.C2876, NewCertificates0089.C2877} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0089.C2878, NewCertificates0089.C2879, NewCertificates0090.C2880, NewCertificates0090.C2881, NewCertificates0090.C2882, NewCertificates0090.C2883, NewCertificates0090.C2884, NewCertificates0090.C2885, NewCertificates0090.C2886, NewCertificates0090.C2887, NewCertificates0090.C2888, NewCertificates0090.C2889, NewCertificates0090.C2890, NewCertificates0090.C2891, NewCertificates0090.C2892, NewCertificates0090.C2893} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0090.C2894, NewCertificates0090.C2895, NewCertificates0090.C2896, NewCertificates0090.C2897, NewCertificates0090.C2898, NewCertificates0090.C2899, NewCertificates0090.C2900, NewCertificates0090.C2901, NewCertificates0090.C2902, NewCertificates0090.C2903, NewCertificates0090.C2904, NewCertificates0090.C2905, NewCertificates0090.C2906, NewCertificates0090.C2907, NewCertificates0090.C2908, NewCertificates0090.C2909} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0089.obstruction2862
  · exact NewCertificates0089.obstruction2863
  · exact NewCertificates0089.obstruction2864
  · exact NewCertificates0089.obstruction2865
  · exact NewCertificates0089.obstruction2866
  · exact NewCertificates0089.obstruction2867
  · exact NewCertificates0089.obstruction2868
  · exact NewCertificates0089.obstruction2869
  · exact NewCertificates0089.obstruction2870
  · exact NewCertificates0089.obstruction2871
  · exact NewCertificates0089.obstruction2872
  · exact NewCertificates0089.obstruction2873
  · exact NewCertificates0089.obstruction2874
  · exact NewCertificates0089.obstruction2875
  · exact NewCertificates0089.obstruction2876
  · exact NewCertificates0089.obstruction2877
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0089.obstruction2878
  · exact NewCertificates0089.obstruction2879
  · exact NewCertificates0090.obstruction2880
  · exact NewCertificates0090.obstruction2881
  · exact NewCertificates0090.obstruction2882
  · exact NewCertificates0090.obstruction2883
  · exact NewCertificates0090.obstruction2884
  · exact NewCertificates0090.obstruction2885
  · exact NewCertificates0090.obstruction2886
  · exact NewCertificates0090.obstruction2887
  · exact NewCertificates0090.obstruction2888
  · exact NewCertificates0090.obstruction2889
  · exact NewCertificates0090.obstruction2890
  · exact NewCertificates0090.obstruction2891
  · exact NewCertificates0090.obstruction2892
  · exact NewCertificates0090.obstruction2893
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0090.obstruction2894
  · exact NewCertificates0090.obstruction2895
  · exact NewCertificates0090.obstruction2896
  · exact NewCertificates0090.obstruction2897
  · exact NewCertificates0090.obstruction2898
  · exact NewCertificates0090.obstruction2899
  · exact NewCertificates0090.obstruction2900
  · exact NewCertificates0090.obstruction2901
  · exact NewCertificates0090.obstruction2902
  · exact NewCertificates0090.obstruction2903
  · exact NewCertificates0090.obstruction2904
  · exact NewCertificates0090.obstruction2905
  · exact NewCertificates0090.obstruction2906
  · exact NewCertificates0090.obstruction2907
  · exact NewCertificates0090.obstruction2908
  · exact NewCertificates0090.obstruction2909
end Nut8.FiniteSupport061
