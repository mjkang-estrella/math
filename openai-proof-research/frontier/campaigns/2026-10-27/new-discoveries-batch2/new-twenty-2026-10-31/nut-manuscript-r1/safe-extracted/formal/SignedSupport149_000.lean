import SupportData149
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport149
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0216.C6924, NewCertificates0216.C6925, NewCertificates0216.C6926, NewCertificates0216.C6927, NewCertificates0216.C6928, NewCertificates0216.C6929, NewCertificates0216.C6930, NewCertificates0216.C6931, NewCertificates0216.C6932, NewCertificates0216.C6933, NewCertificates0216.C6934, NewCertificates0216.C6935, NewCertificates0216.C6936, NewCertificates0216.C6937, NewCertificates0216.C6938, NewCertificates0216.C6939} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0216.C6940, NewCertificates0216.C6941, NewCertificates0216.C6942, NewCertificates0216.C6943, NewCertificates0217.C6944, NewCertificates0217.C6945, NewCertificates0217.C6946, NewCertificates0217.C6947} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0217.C6948, NewCertificates0217.C6949, NewCertificates0217.C6950, NewCertificates0217.C6951, NewCertificates0217.C6952, NewCertificates0217.C6953, NewCertificates0217.C6954, NewCertificates0217.C6955, NewCertificates0217.C6956, NewCertificates0217.C6957, NewCertificates0217.C6958, NewCertificates0217.C6959, NewCertificates0217.C6960, NewCertificates0217.C6961, NewCertificates0217.C6962, NewCertificates0217.C6963} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0217.C6964, NewCertificates0217.C6965, NewCertificates0217.C6966, NewCertificates0217.C6967, NewCertificates0217.C6968, NewCertificates0217.C6969, NewCertificates0217.C6970, NewCertificates0217.C6971} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0216.obstruction6924
  · exact NewCertificates0216.obstruction6925
  · exact NewCertificates0216.obstruction6926
  · exact NewCertificates0216.obstruction6927
  · exact NewCertificates0216.obstruction6928
  · exact NewCertificates0216.obstruction6929
  · exact NewCertificates0216.obstruction6930
  · exact NewCertificates0216.obstruction6931
  · exact NewCertificates0216.obstruction6932
  · exact NewCertificates0216.obstruction6933
  · exact NewCertificates0216.obstruction6934
  · exact NewCertificates0216.obstruction6935
  · exact NewCertificates0216.obstruction6936
  · exact NewCertificates0216.obstruction6937
  · exact NewCertificates0216.obstruction6938
  · exact NewCertificates0216.obstruction6939
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0216.obstruction6940
  · exact NewCertificates0216.obstruction6941
  · exact NewCertificates0216.obstruction6942
  · exact NewCertificates0216.obstruction6943
  · exact NewCertificates0217.obstruction6944
  · exact NewCertificates0217.obstruction6945
  · exact NewCertificates0217.obstruction6946
  · exact NewCertificates0217.obstruction6947
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0217.obstruction6948
  · exact NewCertificates0217.obstruction6949
  · exact NewCertificates0217.obstruction6950
  · exact NewCertificates0217.obstruction6951
  · exact NewCertificates0217.obstruction6952
  · exact NewCertificates0217.obstruction6953
  · exact NewCertificates0217.obstruction6954
  · exact NewCertificates0217.obstruction6955
  · exact NewCertificates0217.obstruction6956
  · exact NewCertificates0217.obstruction6957
  · exact NewCertificates0217.obstruction6958
  · exact NewCertificates0217.obstruction6959
  · exact NewCertificates0217.obstruction6960
  · exact NewCertificates0217.obstruction6961
  · exact NewCertificates0217.obstruction6962
  · exact NewCertificates0217.obstruction6963
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0217.obstruction6964
  · exact NewCertificates0217.obstruction6965
  · exact NewCertificates0217.obstruction6966
  · exact NewCertificates0217.obstruction6967
  · exact NewCertificates0217.obstruction6968
  · exact NewCertificates0217.obstruction6969
  · exact NewCertificates0217.obstruction6970
  · exact NewCertificates0217.obstruction6971
end Nut8.FiniteSupport149
