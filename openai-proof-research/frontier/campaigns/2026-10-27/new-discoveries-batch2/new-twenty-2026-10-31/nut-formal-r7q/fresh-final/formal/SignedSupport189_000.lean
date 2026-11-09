import SupportData189
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport189
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0278.C8924, NewCertificates0278.C8925, NewCertificates0278.C8926, NewCertificates0278.C8927, NewCertificates0279.C8928, NewCertificates0279.C8929, NewCertificates0279.C8930, NewCertificates0279.C8931, NewCertificates0279.C8932, NewCertificates0279.C8933, NewCertificates0279.C8934, NewCertificates0279.C8935, NewCertificates0279.C8936, NewCertificates0279.C8937, NewCertificates0279.C8938, NewCertificates0279.C8939} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0279.C8940, NewCertificates0279.C8941, NewCertificates0279.C8942, NewCertificates0279.C8943, NewCertificates0279.C8944, NewCertificates0279.C8945, NewCertificates0279.C8946, NewCertificates0279.C8947, NewCertificates0279.C8948, NewCertificates0279.C8949, NewCertificates0279.C8950, NewCertificates0279.C8951, NewCertificates0279.C8952, NewCertificates0279.C8953, NewCertificates0279.C8954, NewCertificates0279.C8955} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0279.C8956, NewCertificates0279.C8957, NewCertificates0279.C8958, NewCertificates0279.C8959, NewCertificates0280.C8960, NewCertificates0280.C8961, NewCertificates0280.C8962, NewCertificates0280.C8963, NewCertificates0280.C8964, NewCertificates0280.C8965, NewCertificates0280.C8966, NewCertificates0280.C8967, NewCertificates0280.C8968, NewCertificates0280.C8969, NewCertificates0280.C8970, NewCertificates0280.C8971} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0280.C8972, NewCertificates0280.C8973, NewCertificates0280.C8974, NewCertificates0280.C8975, NewCertificates0280.C8976, NewCertificates0280.C8977, NewCertificates0280.C8978, NewCertificates0280.C8979} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0278.obstruction8924
  · exact NewCertificates0278.obstruction8925
  · exact NewCertificates0278.obstruction8926
  · exact NewCertificates0278.obstruction8927
  · exact NewCertificates0279.obstruction8928
  · exact NewCertificates0279.obstruction8929
  · exact NewCertificates0279.obstruction8930
  · exact NewCertificates0279.obstruction8931
  · exact NewCertificates0279.obstruction8932
  · exact NewCertificates0279.obstruction8933
  · exact NewCertificates0279.obstruction8934
  · exact NewCertificates0279.obstruction8935
  · exact NewCertificates0279.obstruction8936
  · exact NewCertificates0279.obstruction8937
  · exact NewCertificates0279.obstruction8938
  · exact NewCertificates0279.obstruction8939
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0279.obstruction8940
  · exact NewCertificates0279.obstruction8941
  · exact NewCertificates0279.obstruction8942
  · exact NewCertificates0279.obstruction8943
  · exact NewCertificates0279.obstruction8944
  · exact NewCertificates0279.obstruction8945
  · exact NewCertificates0279.obstruction8946
  · exact NewCertificates0279.obstruction8947
  · exact NewCertificates0279.obstruction8948
  · exact NewCertificates0279.obstruction8949
  · exact NewCertificates0279.obstruction8950
  · exact NewCertificates0279.obstruction8951
  · exact NewCertificates0279.obstruction8952
  · exact NewCertificates0279.obstruction8953
  · exact NewCertificates0279.obstruction8954
  · exact NewCertificates0279.obstruction8955
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0279.obstruction8956
  · exact NewCertificates0279.obstruction8957
  · exact NewCertificates0279.obstruction8958
  · exact NewCertificates0279.obstruction8959
  · exact NewCertificates0280.obstruction8960
  · exact NewCertificates0280.obstruction8961
  · exact NewCertificates0280.obstruction8962
  · exact NewCertificates0280.obstruction8963
  · exact NewCertificates0280.obstruction8964
  · exact NewCertificates0280.obstruction8965
  · exact NewCertificates0280.obstruction8966
  · exact NewCertificates0280.obstruction8967
  · exact NewCertificates0280.obstruction8968
  · exact NewCertificates0280.obstruction8969
  · exact NewCertificates0280.obstruction8970
  · exact NewCertificates0280.obstruction8971
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0280.obstruction8972
  · exact NewCertificates0280.obstruction8973
  · exact NewCertificates0280.obstruction8974
  · exact NewCertificates0280.obstruction8975
  · exact NewCertificates0280.obstruction8976
  · exact NewCertificates0280.obstruction8977
  · exact NewCertificates0280.obstruction8978
  · exact NewCertificates0280.obstruction8979
end Nut8.FiniteSupport189
