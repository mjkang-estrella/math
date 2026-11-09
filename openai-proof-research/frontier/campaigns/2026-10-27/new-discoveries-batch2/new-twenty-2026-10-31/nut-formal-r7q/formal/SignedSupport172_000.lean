import SupportData172
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport172
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0248.C7956, NewCertificates0248.C7957, NewCertificates0248.C7958, NewCertificates0248.C7959, NewCertificates0248.C7960, NewCertificates0248.C7961, NewCertificates0248.C7962, NewCertificates0248.C7963, NewCertificates0248.C7964, NewCertificates0248.C7965, NewCertificates0248.C7966, NewCertificates0248.C7967, NewCertificates0249.C7968, NewCertificates0249.C7969, NewCertificates0249.C7970, NewCertificates0249.C7971} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0249.C7972, NewCertificates0249.C7973, NewCertificates0249.C7974, NewCertificates0249.C7975, NewCertificates0249.C7976, NewCertificates0249.C7977, NewCertificates0249.C7978, NewCertificates0249.C7979, NewCertificates0249.C7980, NewCertificates0249.C7981, NewCertificates0249.C7982, NewCertificates0249.C7983, NewCertificates0249.C7984, NewCertificates0249.C7985, NewCertificates0249.C7986, NewCertificates0249.C7987} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0249.C7988, NewCertificates0249.C7989, NewCertificates0249.C7990, NewCertificates0249.C7991, NewCertificates0249.C7992, NewCertificates0249.C7993, NewCertificates0249.C7994, NewCertificates0249.C7995} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0249.C7996, NewCertificates0249.C7997, NewCertificates0249.C7998, NewCertificates0249.C7999, NewCertificates0250.C8000, NewCertificates0250.C8001, NewCertificates0250.C8002, NewCertificates0250.C8003} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0248.obstruction7956
  · exact NewCertificates0248.obstruction7957
  · exact NewCertificates0248.obstruction7958
  · exact NewCertificates0248.obstruction7959
  · exact NewCertificates0248.obstruction7960
  · exact NewCertificates0248.obstruction7961
  · exact NewCertificates0248.obstruction7962
  · exact NewCertificates0248.obstruction7963
  · exact NewCertificates0248.obstruction7964
  · exact NewCertificates0248.obstruction7965
  · exact NewCertificates0248.obstruction7966
  · exact NewCertificates0248.obstruction7967
  · exact NewCertificates0249.obstruction7968
  · exact NewCertificates0249.obstruction7969
  · exact NewCertificates0249.obstruction7970
  · exact NewCertificates0249.obstruction7971
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0249.obstruction7972
  · exact NewCertificates0249.obstruction7973
  · exact NewCertificates0249.obstruction7974
  · exact NewCertificates0249.obstruction7975
  · exact NewCertificates0249.obstruction7976
  · exact NewCertificates0249.obstruction7977
  · exact NewCertificates0249.obstruction7978
  · exact NewCertificates0249.obstruction7979
  · exact NewCertificates0249.obstruction7980
  · exact NewCertificates0249.obstruction7981
  · exact NewCertificates0249.obstruction7982
  · exact NewCertificates0249.obstruction7983
  · exact NewCertificates0249.obstruction7984
  · exact NewCertificates0249.obstruction7985
  · exact NewCertificates0249.obstruction7986
  · exact NewCertificates0249.obstruction7987
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0249.obstruction7988
  · exact NewCertificates0249.obstruction7989
  · exact NewCertificates0249.obstruction7990
  · exact NewCertificates0249.obstruction7991
  · exact NewCertificates0249.obstruction7992
  · exact NewCertificates0249.obstruction7993
  · exact NewCertificates0249.obstruction7994
  · exact NewCertificates0249.obstruction7995
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0249.obstruction7996
  · exact NewCertificates0249.obstruction7997
  · exact NewCertificates0249.obstruction7998
  · exact NewCertificates0249.obstruction7999
  · exact NewCertificates0250.obstruction8000
  · exact NewCertificates0250.obstruction8001
  · exact NewCertificates0250.obstruction8002
  · exact NewCertificates0250.obstruction8003
end Nut8.FiniteSupport172
