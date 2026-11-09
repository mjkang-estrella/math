import SupportData062
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport062
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0090.C2910, NewCertificates0090.C2911, NewCertificates0091.C2912, NewCertificates0091.C2913, NewCertificates0091.C2914, NewCertificates0091.C2915, NewCertificates0091.C2916, NewCertificates0091.C2917, NewCertificates0091.C2918, NewCertificates0091.C2919, NewCertificates0091.C2920, NewCertificates0091.C2921, NewCertificates0091.C2922, NewCertificates0091.C2923, NewCertificates0091.C2924, NewCertificates0091.C2925, NewCertificates0091.C2926, NewCertificates0091.C2927, NewCertificates0091.C2928, NewCertificates0091.C2929, NewCertificates0091.C2930, NewCertificates0091.C2931, NewCertificates0091.C2932, NewCertificates0091.C2933, NewCertificates0091.C2934, NewCertificates0091.C2935, NewCertificates0091.C2936, NewCertificates0091.C2937, NewCertificates0091.C2938, NewCertificates0091.C2939, NewCertificates0091.C2940, NewCertificates0091.C2941} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0090.obstruction2910
  · exact NewCertificates0090.obstruction2911
  · exact NewCertificates0091.obstruction2912
  · exact NewCertificates0091.obstruction2913
  · exact NewCertificates0091.obstruction2914
  · exact NewCertificates0091.obstruction2915
  · exact NewCertificates0091.obstruction2916
  · exact NewCertificates0091.obstruction2917
  · exact NewCertificates0091.obstruction2918
  · exact NewCertificates0091.obstruction2919
  · exact NewCertificates0091.obstruction2920
  · exact NewCertificates0091.obstruction2921
  · exact NewCertificates0091.obstruction2922
  · exact NewCertificates0091.obstruction2923
  · exact NewCertificates0091.obstruction2924
  · exact NewCertificates0091.obstruction2925
  · exact NewCertificates0091.obstruction2926
  · exact NewCertificates0091.obstruction2927
  · exact NewCertificates0091.obstruction2928
  · exact NewCertificates0091.obstruction2929
  · exact NewCertificates0091.obstruction2930
  · exact NewCertificates0091.obstruction2931
  · exact NewCertificates0091.obstruction2932
  · exact NewCertificates0091.obstruction2933
  · exact NewCertificates0091.obstruction2934
  · exact NewCertificates0091.obstruction2935
  · exact NewCertificates0091.obstruction2936
  · exact NewCertificates0091.obstruction2937
  · exact NewCertificates0091.obstruction2938
  · exact NewCertificates0091.obstruction2939
  · exact NewCertificates0091.obstruction2940
  · exact NewCertificates0091.obstruction2941
end Nut8.FiniteSupport062
