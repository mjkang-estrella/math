import SupportData020
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport020
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0029.C936, NewCertificates0029.C937, NewCertificates0029.C938, NewCertificates0029.C939, NewCertificates0029.C940, NewCertificates0029.C941, NewCertificates0029.C942, NewCertificates0029.C943, NewCertificates0029.C944, NewCertificates0029.C945, NewCertificates0029.C946, NewCertificates0029.C947, NewCertificates0029.C948, NewCertificates0029.C949, NewCertificates0029.C950, NewCertificates0029.C951, NewCertificates0029.C952, NewCertificates0029.C953, NewCertificates0029.C954, NewCertificates0029.C955, NewCertificates0029.C956, NewCertificates0029.C957, NewCertificates0029.C958, NewCertificates0029.C959, NewCertificates0030.C960, NewCertificates0030.C961, NewCertificates0030.C962, NewCertificates0030.C963, NewCertificates0030.C964, NewCertificates0030.C965, NewCertificates0030.C966, NewCertificates0030.C967} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0030.C968, NewCertificates0030.C969, NewCertificates0030.C970, NewCertificates0030.C971, NewCertificates0030.C972, NewCertificates0030.C973, NewCertificates0030.C974, NewCertificates0030.C975, NewCertificates0030.C976, NewCertificates0030.C977, NewCertificates0030.C978, NewCertificates0030.C979, NewCertificates0030.C980, NewCertificates0030.C981, NewCertificates0030.C982, NewCertificates0030.C983} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0029.obstruction936
  · exact NewCertificates0029.obstruction937
  · exact NewCertificates0029.obstruction938
  · exact NewCertificates0029.obstruction939
  · exact NewCertificates0029.obstruction940
  · exact NewCertificates0029.obstruction941
  · exact NewCertificates0029.obstruction942
  · exact NewCertificates0029.obstruction943
  · exact NewCertificates0029.obstruction944
  · exact NewCertificates0029.obstruction945
  · exact NewCertificates0029.obstruction946
  · exact NewCertificates0029.obstruction947
  · exact NewCertificates0029.obstruction948
  · exact NewCertificates0029.obstruction949
  · exact NewCertificates0029.obstruction950
  · exact NewCertificates0029.obstruction951
  · exact NewCertificates0029.obstruction952
  · exact NewCertificates0029.obstruction953
  · exact NewCertificates0029.obstruction954
  · exact NewCertificates0029.obstruction955
  · exact NewCertificates0029.obstruction956
  · exact NewCertificates0029.obstruction957
  · exact NewCertificates0029.obstruction958
  · exact NewCertificates0029.obstruction959
  · exact NewCertificates0030.obstruction960
  · exact NewCertificates0030.obstruction961
  · exact NewCertificates0030.obstruction962
  · exact NewCertificates0030.obstruction963
  · exact NewCertificates0030.obstruction964
  · exact NewCertificates0030.obstruction965
  · exact NewCertificates0030.obstruction966
  · exact NewCertificates0030.obstruction967
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0030.obstruction968
  · exact NewCertificates0030.obstruction969
  · exact NewCertificates0030.obstruction970
  · exact NewCertificates0030.obstruction971
  · exact NewCertificates0030.obstruction972
  · exact NewCertificates0030.obstruction973
  · exact NewCertificates0030.obstruction974
  · exact NewCertificates0030.obstruction975
  · exact NewCertificates0030.obstruction976
  · exact NewCertificates0030.obstruction977
  · exact NewCertificates0030.obstruction978
  · exact NewCertificates0030.obstruction979
  · exact NewCertificates0030.obstruction980
  · exact NewCertificates0030.obstruction981
  · exact NewCertificates0030.obstruction982
  · exact NewCertificates0030.obstruction983
end Nut8.FiniteSupport020
