import SupportData064
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport064
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0092.C2974, NewCertificates0092.C2975, NewCertificates0093.C2976, NewCertificates0093.C2977, NewCertificates0093.C2978, NewCertificates0093.C2979, NewCertificates0093.C2980, NewCertificates0093.C2981, NewCertificates0093.C2982, NewCertificates0093.C2983, NewCertificates0093.C2984, NewCertificates0093.C2985, NewCertificates0093.C2986, NewCertificates0093.C2987, NewCertificates0093.C2988, NewCertificates0093.C2989} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0093.C2990, NewCertificates0093.C2991, NewCertificates0093.C2992, NewCertificates0093.C2993, NewCertificates0093.C2994, NewCertificates0093.C2995, NewCertificates0093.C2996, NewCertificates0093.C2997} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0093.C2998, NewCertificates0093.C2999, NewCertificates0093.C3000, NewCertificates0093.C3001, NewCertificates0093.C3002, NewCertificates0093.C3003, NewCertificates0093.C3004, NewCertificates0093.C3005, NewCertificates0093.C3006, NewCertificates0093.C3007, NewCertificates0094.C3008, NewCertificates0094.C3009, NewCertificates0094.C3010, NewCertificates0094.C3011, NewCertificates0094.C3012, NewCertificates0094.C3013} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0092.obstruction2974
  · exact NewCertificates0092.obstruction2975
  · exact NewCertificates0093.obstruction2976
  · exact NewCertificates0093.obstruction2977
  · exact NewCertificates0093.obstruction2978
  · exact NewCertificates0093.obstruction2979
  · exact NewCertificates0093.obstruction2980
  · exact NewCertificates0093.obstruction2981
  · exact NewCertificates0093.obstruction2982
  · exact NewCertificates0093.obstruction2983
  · exact NewCertificates0093.obstruction2984
  · exact NewCertificates0093.obstruction2985
  · exact NewCertificates0093.obstruction2986
  · exact NewCertificates0093.obstruction2987
  · exact NewCertificates0093.obstruction2988
  · exact NewCertificates0093.obstruction2989
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0093.obstruction2990
  · exact NewCertificates0093.obstruction2991
  · exact NewCertificates0093.obstruction2992
  · exact NewCertificates0093.obstruction2993
  · exact NewCertificates0093.obstruction2994
  · exact NewCertificates0093.obstruction2995
  · exact NewCertificates0093.obstruction2996
  · exact NewCertificates0093.obstruction2997
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0093.obstruction2998
  · exact NewCertificates0093.obstruction2999
  · exact NewCertificates0093.obstruction3000
  · exact NewCertificates0093.obstruction3001
  · exact NewCertificates0093.obstruction3002
  · exact NewCertificates0093.obstruction3003
  · exact NewCertificates0093.obstruction3004
  · exact NewCertificates0093.obstruction3005
  · exact NewCertificates0093.obstruction3006
  · exact NewCertificates0093.obstruction3007
  · exact NewCertificates0094.obstruction3008
  · exact NewCertificates0094.obstruction3009
  · exact NewCertificates0094.obstruction3010
  · exact NewCertificates0094.obstruction3011
  · exact NewCertificates0094.obstruction3012
  · exact NewCertificates0094.obstruction3013
end Nut8.FiniteSupport064
