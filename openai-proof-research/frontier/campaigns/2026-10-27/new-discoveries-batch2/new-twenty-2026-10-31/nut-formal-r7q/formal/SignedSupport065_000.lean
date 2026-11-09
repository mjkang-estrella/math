import SupportData065
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport065
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0094.C3014, NewCertificates0094.C3015, NewCertificates0094.C3016, NewCertificates0094.C3017, NewCertificates0094.C3018, NewCertificates0094.C3019, NewCertificates0094.C3020, NewCertificates0094.C3021, NewCertificates0094.C3022, NewCertificates0094.C3023, NewCertificates0094.C3024, NewCertificates0094.C3025, NewCertificates0094.C3026, NewCertificates0094.C3027, NewCertificates0094.C3028, NewCertificates0094.C3029} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0094.C3030, NewCertificates0094.C3031, NewCertificates0094.C3032, NewCertificates0094.C3033, NewCertificates0094.C3034, NewCertificates0094.C3035, NewCertificates0094.C3036, NewCertificates0094.C3037} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0094.C3038, NewCertificates0094.C3039, NewCertificates0095.C3040, NewCertificates0095.C3041, NewCertificates0095.C3042, NewCertificates0095.C3043, NewCertificates0095.C3044, NewCertificates0095.C3045, NewCertificates0095.C3046, NewCertificates0095.C3047, NewCertificates0095.C3048, NewCertificates0095.C3049, NewCertificates0095.C3050, NewCertificates0095.C3051, NewCertificates0095.C3052, NewCertificates0095.C3053} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0095.C3054, NewCertificates0095.C3055, NewCertificates0095.C3056, NewCertificates0095.C3057, NewCertificates0095.C3058, NewCertificates0095.C3059, NewCertificates0095.C3060, NewCertificates0095.C3061} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0094.obstruction3014
  · exact NewCertificates0094.obstruction3015
  · exact NewCertificates0094.obstruction3016
  · exact NewCertificates0094.obstruction3017
  · exact NewCertificates0094.obstruction3018
  · exact NewCertificates0094.obstruction3019
  · exact NewCertificates0094.obstruction3020
  · exact NewCertificates0094.obstruction3021
  · exact NewCertificates0094.obstruction3022
  · exact NewCertificates0094.obstruction3023
  · exact NewCertificates0094.obstruction3024
  · exact NewCertificates0094.obstruction3025
  · exact NewCertificates0094.obstruction3026
  · exact NewCertificates0094.obstruction3027
  · exact NewCertificates0094.obstruction3028
  · exact NewCertificates0094.obstruction3029
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0094.obstruction3030
  · exact NewCertificates0094.obstruction3031
  · exact NewCertificates0094.obstruction3032
  · exact NewCertificates0094.obstruction3033
  · exact NewCertificates0094.obstruction3034
  · exact NewCertificates0094.obstruction3035
  · exact NewCertificates0094.obstruction3036
  · exact NewCertificates0094.obstruction3037
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0094.obstruction3038
  · exact NewCertificates0094.obstruction3039
  · exact NewCertificates0095.obstruction3040
  · exact NewCertificates0095.obstruction3041
  · exact NewCertificates0095.obstruction3042
  · exact NewCertificates0095.obstruction3043
  · exact NewCertificates0095.obstruction3044
  · exact NewCertificates0095.obstruction3045
  · exact NewCertificates0095.obstruction3046
  · exact NewCertificates0095.obstruction3047
  · exact NewCertificates0095.obstruction3048
  · exact NewCertificates0095.obstruction3049
  · exact NewCertificates0095.obstruction3050
  · exact NewCertificates0095.obstruction3051
  · exact NewCertificates0095.obstruction3052
  · exact NewCertificates0095.obstruction3053
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0095.obstruction3054
  · exact NewCertificates0095.obstruction3055
  · exact NewCertificates0095.obstruction3056
  · exact NewCertificates0095.obstruction3057
  · exact NewCertificates0095.obstruction3058
  · exact NewCertificates0095.obstruction3059
  · exact NewCertificates0095.obstruction3060
  · exact NewCertificates0095.obstruction3061
end Nut8.FiniteSupport065
