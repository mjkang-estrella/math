import SupportData171
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport171
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0247.C7908, NewCertificates0247.C7909, NewCertificates0247.C7910, NewCertificates0247.C7911, NewCertificates0247.C7912, NewCertificates0247.C7913, NewCertificates0247.C7914, NewCertificates0247.C7915, NewCertificates0247.C7916, NewCertificates0247.C7917, NewCertificates0247.C7918, NewCertificates0247.C7919, NewCertificates0247.C7920, NewCertificates0247.C7921, NewCertificates0247.C7922, NewCertificates0247.C7923} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0247.C7924, NewCertificates0247.C7925, NewCertificates0247.C7926, NewCertificates0247.C7927, NewCertificates0247.C7928, NewCertificates0247.C7929, NewCertificates0247.C7930, NewCertificates0247.C7931, NewCertificates0247.C7932, NewCertificates0247.C7933, NewCertificates0247.C7934, NewCertificates0247.C7935, NewCertificates0248.C7936, NewCertificates0248.C7937, NewCertificates0248.C7938, NewCertificates0248.C7939} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0248.C7940, NewCertificates0248.C7941, NewCertificates0248.C7942, NewCertificates0248.C7943, NewCertificates0248.C7944, NewCertificates0248.C7945, NewCertificates0248.C7946, NewCertificates0248.C7947} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0248.C7948, NewCertificates0248.C7949, NewCertificates0248.C7950, NewCertificates0248.C7951, NewCertificates0248.C7952, NewCertificates0248.C7953, NewCertificates0248.C7954, NewCertificates0248.C7955} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0247.obstruction7908
  · exact NewCertificates0247.obstruction7909
  · exact NewCertificates0247.obstruction7910
  · exact NewCertificates0247.obstruction7911
  · exact NewCertificates0247.obstruction7912
  · exact NewCertificates0247.obstruction7913
  · exact NewCertificates0247.obstruction7914
  · exact NewCertificates0247.obstruction7915
  · exact NewCertificates0247.obstruction7916
  · exact NewCertificates0247.obstruction7917
  · exact NewCertificates0247.obstruction7918
  · exact NewCertificates0247.obstruction7919
  · exact NewCertificates0247.obstruction7920
  · exact NewCertificates0247.obstruction7921
  · exact NewCertificates0247.obstruction7922
  · exact NewCertificates0247.obstruction7923
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0247.obstruction7924
  · exact NewCertificates0247.obstruction7925
  · exact NewCertificates0247.obstruction7926
  · exact NewCertificates0247.obstruction7927
  · exact NewCertificates0247.obstruction7928
  · exact NewCertificates0247.obstruction7929
  · exact NewCertificates0247.obstruction7930
  · exact NewCertificates0247.obstruction7931
  · exact NewCertificates0247.obstruction7932
  · exact NewCertificates0247.obstruction7933
  · exact NewCertificates0247.obstruction7934
  · exact NewCertificates0247.obstruction7935
  · exact NewCertificates0248.obstruction7936
  · exact NewCertificates0248.obstruction7937
  · exact NewCertificates0248.obstruction7938
  · exact NewCertificates0248.obstruction7939
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0248.obstruction7940
  · exact NewCertificates0248.obstruction7941
  · exact NewCertificates0248.obstruction7942
  · exact NewCertificates0248.obstruction7943
  · exact NewCertificates0248.obstruction7944
  · exact NewCertificates0248.obstruction7945
  · exact NewCertificates0248.obstruction7946
  · exact NewCertificates0248.obstruction7947
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0248.obstruction7948
  · exact NewCertificates0248.obstruction7949
  · exact NewCertificates0248.obstruction7950
  · exact NewCertificates0248.obstruction7951
  · exact NewCertificates0248.obstruction7952
  · exact NewCertificates0248.obstruction7953
  · exact NewCertificates0248.obstruction7954
  · exact NewCertificates0248.obstruction7955
end Nut8.FiniteSupport171
