import SupportData067
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport067
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0097.C3110, NewCertificates0097.C3111, NewCertificates0097.C3112, NewCertificates0097.C3113, NewCertificates0097.C3114, NewCertificates0097.C3115, NewCertificates0097.C3116, NewCertificates0097.C3117, NewCertificates0097.C3118, NewCertificates0097.C3119, NewCertificates0097.C3120, NewCertificates0097.C3121, NewCertificates0097.C3122, NewCertificates0097.C3123, NewCertificates0097.C3124, NewCertificates0097.C3125} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0097.C3126, NewCertificates0097.C3127, NewCertificates0097.C3128, NewCertificates0097.C3129, NewCertificates0097.C3130, NewCertificates0097.C3131, NewCertificates0097.C3132, NewCertificates0097.C3133} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0097.C3134, NewCertificates0097.C3135, NewCertificates0098.C3136, NewCertificates0098.C3137, NewCertificates0098.C3138, NewCertificates0098.C3139, NewCertificates0098.C3140, NewCertificates0098.C3141, NewCertificates0098.C3142, NewCertificates0098.C3143, NewCertificates0098.C3144, NewCertificates0098.C3145, NewCertificates0098.C3146, NewCertificates0098.C3147, NewCertificates0098.C3148, NewCertificates0098.C3149} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0098.C3150, NewCertificates0098.C3151, NewCertificates0098.C3152, NewCertificates0098.C3153, NewCertificates0098.C3154, NewCertificates0098.C3155, NewCertificates0098.C3156, NewCertificates0098.C3157, NewCertificates0098.C3158, NewCertificates0098.C3159, NewCertificates0098.C3160, NewCertificates0098.C3161, NewCertificates0098.C3162, NewCertificates0098.C3163, NewCertificates0098.C3164, NewCertificates0098.C3165} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0097.obstruction3110
  · exact NewCertificates0097.obstruction3111
  · exact NewCertificates0097.obstruction3112
  · exact NewCertificates0097.obstruction3113
  · exact NewCertificates0097.obstruction3114
  · exact NewCertificates0097.obstruction3115
  · exact NewCertificates0097.obstruction3116
  · exact NewCertificates0097.obstruction3117
  · exact NewCertificates0097.obstruction3118
  · exact NewCertificates0097.obstruction3119
  · exact NewCertificates0097.obstruction3120
  · exact NewCertificates0097.obstruction3121
  · exact NewCertificates0097.obstruction3122
  · exact NewCertificates0097.obstruction3123
  · exact NewCertificates0097.obstruction3124
  · exact NewCertificates0097.obstruction3125
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0097.obstruction3126
  · exact NewCertificates0097.obstruction3127
  · exact NewCertificates0097.obstruction3128
  · exact NewCertificates0097.obstruction3129
  · exact NewCertificates0097.obstruction3130
  · exact NewCertificates0097.obstruction3131
  · exact NewCertificates0097.obstruction3132
  · exact NewCertificates0097.obstruction3133
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0097.obstruction3134
  · exact NewCertificates0097.obstruction3135
  · exact NewCertificates0098.obstruction3136
  · exact NewCertificates0098.obstruction3137
  · exact NewCertificates0098.obstruction3138
  · exact NewCertificates0098.obstruction3139
  · exact NewCertificates0098.obstruction3140
  · exact NewCertificates0098.obstruction3141
  · exact NewCertificates0098.obstruction3142
  · exact NewCertificates0098.obstruction3143
  · exact NewCertificates0098.obstruction3144
  · exact NewCertificates0098.obstruction3145
  · exact NewCertificates0098.obstruction3146
  · exact NewCertificates0098.obstruction3147
  · exact NewCertificates0098.obstruction3148
  · exact NewCertificates0098.obstruction3149
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0098.obstruction3150
  · exact NewCertificates0098.obstruction3151
  · exact NewCertificates0098.obstruction3152
  · exact NewCertificates0098.obstruction3153
  · exact NewCertificates0098.obstruction3154
  · exact NewCertificates0098.obstruction3155
  · exact NewCertificates0098.obstruction3156
  · exact NewCertificates0098.obstruction3157
  · exact NewCertificates0098.obstruction3158
  · exact NewCertificates0098.obstruction3159
  · exact NewCertificates0098.obstruction3160
  · exact NewCertificates0098.obstruction3161
  · exact NewCertificates0098.obstruction3162
  · exact NewCertificates0098.obstruction3163
  · exact NewCertificates0098.obstruction3164
  · exact NewCertificates0098.obstruction3165
end Nut8.FiniteSupport067
