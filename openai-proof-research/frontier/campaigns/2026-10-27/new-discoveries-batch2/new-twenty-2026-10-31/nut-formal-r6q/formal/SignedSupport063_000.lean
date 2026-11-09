import SupportData063
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport063
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0091.C2942, NewCertificates0091.C2943, NewCertificates0092.C2944, NewCertificates0092.C2945, NewCertificates0092.C2946, NewCertificates0092.C2947, NewCertificates0092.C2948, NewCertificates0092.C2949, NewCertificates0092.C2950, NewCertificates0092.C2951, NewCertificates0092.C2952, NewCertificates0092.C2953, NewCertificates0092.C2954, NewCertificates0092.C2955, NewCertificates0092.C2956, NewCertificates0092.C2957, NewCertificates0092.C2958, NewCertificates0092.C2959, NewCertificates0092.C2960, NewCertificates0092.C2961, NewCertificates0092.C2962, NewCertificates0092.C2963, NewCertificates0092.C2964, NewCertificates0092.C2965, NewCertificates0092.C2966, NewCertificates0092.C2967, NewCertificates0092.C2968, NewCertificates0092.C2969, NewCertificates0092.C2970, NewCertificates0092.C2971, NewCertificates0092.C2972, NewCertificates0092.C2973} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0091.obstruction2942
  · exact NewCertificates0091.obstruction2943
  · exact NewCertificates0092.obstruction2944
  · exact NewCertificates0092.obstruction2945
  · exact NewCertificates0092.obstruction2946
  · exact NewCertificates0092.obstruction2947
  · exact NewCertificates0092.obstruction2948
  · exact NewCertificates0092.obstruction2949
  · exact NewCertificates0092.obstruction2950
  · exact NewCertificates0092.obstruction2951
  · exact NewCertificates0092.obstruction2952
  · exact NewCertificates0092.obstruction2953
  · exact NewCertificates0092.obstruction2954
  · exact NewCertificates0092.obstruction2955
  · exact NewCertificates0092.obstruction2956
  · exact NewCertificates0092.obstruction2957
  · exact NewCertificates0092.obstruction2958
  · exact NewCertificates0092.obstruction2959
  · exact NewCertificates0092.obstruction2960
  · exact NewCertificates0092.obstruction2961
  · exact NewCertificates0092.obstruction2962
  · exact NewCertificates0092.obstruction2963
  · exact NewCertificates0092.obstruction2964
  · exact NewCertificates0092.obstruction2965
  · exact NewCertificates0092.obstruction2966
  · exact NewCertificates0092.obstruction2967
  · exact NewCertificates0092.obstruction2968
  · exact NewCertificates0092.obstruction2969
  · exact NewCertificates0092.obstruction2970
  · exact NewCertificates0092.obstruction2971
  · exact NewCertificates0092.obstruction2972
  · exact NewCertificates0092.obstruction2973
end Nut8.FiniteSupport063
