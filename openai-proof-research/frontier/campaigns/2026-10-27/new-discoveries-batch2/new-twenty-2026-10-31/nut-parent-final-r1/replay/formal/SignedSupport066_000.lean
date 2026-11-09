import SupportData066
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport066
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0095.C3062, NewCertificates0095.C3063, NewCertificates0095.C3064, NewCertificates0095.C3065, NewCertificates0095.C3066, NewCertificates0095.C3067, NewCertificates0095.C3068, NewCertificates0095.C3069, NewCertificates0095.C3070, NewCertificates0095.C3071, NewCertificates0096.C3072, NewCertificates0096.C3073, NewCertificates0096.C3074, NewCertificates0096.C3075, NewCertificates0096.C3076, NewCertificates0096.C3077} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0096.C3078, NewCertificates0096.C3079, NewCertificates0096.C3080, NewCertificates0096.C3081, NewCertificates0096.C3082, NewCertificates0096.C3083, NewCertificates0096.C3084, NewCertificates0096.C3085, NewCertificates0096.C3086, NewCertificates0096.C3087, NewCertificates0096.C3088, NewCertificates0096.C3089, NewCertificates0096.C3090, NewCertificates0096.C3091, NewCertificates0096.C3092, NewCertificates0096.C3093} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0096.C3094, NewCertificates0096.C3095, NewCertificates0096.C3096, NewCertificates0096.C3097, NewCertificates0096.C3098, NewCertificates0096.C3099, NewCertificates0096.C3100, NewCertificates0096.C3101} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0096.C3102, NewCertificates0096.C3103, NewCertificates0097.C3104, NewCertificates0097.C3105, NewCertificates0097.C3106, NewCertificates0097.C3107, NewCertificates0097.C3108, NewCertificates0097.C3109} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0095.obstruction3062
  · exact NewCertificates0095.obstruction3063
  · exact NewCertificates0095.obstruction3064
  · exact NewCertificates0095.obstruction3065
  · exact NewCertificates0095.obstruction3066
  · exact NewCertificates0095.obstruction3067
  · exact NewCertificates0095.obstruction3068
  · exact NewCertificates0095.obstruction3069
  · exact NewCertificates0095.obstruction3070
  · exact NewCertificates0095.obstruction3071
  · exact NewCertificates0096.obstruction3072
  · exact NewCertificates0096.obstruction3073
  · exact NewCertificates0096.obstruction3074
  · exact NewCertificates0096.obstruction3075
  · exact NewCertificates0096.obstruction3076
  · exact NewCertificates0096.obstruction3077
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0096.obstruction3078
  · exact NewCertificates0096.obstruction3079
  · exact NewCertificates0096.obstruction3080
  · exact NewCertificates0096.obstruction3081
  · exact NewCertificates0096.obstruction3082
  · exact NewCertificates0096.obstruction3083
  · exact NewCertificates0096.obstruction3084
  · exact NewCertificates0096.obstruction3085
  · exact NewCertificates0096.obstruction3086
  · exact NewCertificates0096.obstruction3087
  · exact NewCertificates0096.obstruction3088
  · exact NewCertificates0096.obstruction3089
  · exact NewCertificates0096.obstruction3090
  · exact NewCertificates0096.obstruction3091
  · exact NewCertificates0096.obstruction3092
  · exact NewCertificates0096.obstruction3093
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0096.obstruction3094
  · exact NewCertificates0096.obstruction3095
  · exact NewCertificates0096.obstruction3096
  · exact NewCertificates0096.obstruction3097
  · exact NewCertificates0096.obstruction3098
  · exact NewCertificates0096.obstruction3099
  · exact NewCertificates0096.obstruction3100
  · exact NewCertificates0096.obstruction3101
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0096.obstruction3102
  · exact NewCertificates0096.obstruction3103
  · exact NewCertificates0097.obstruction3104
  · exact NewCertificates0097.obstruction3105
  · exact NewCertificates0097.obstruction3106
  · exact NewCertificates0097.obstruction3107
  · exact NewCertificates0097.obstruction3108
  · exact NewCertificates0097.obstruction3109
end Nut8.FiniteSupport066
