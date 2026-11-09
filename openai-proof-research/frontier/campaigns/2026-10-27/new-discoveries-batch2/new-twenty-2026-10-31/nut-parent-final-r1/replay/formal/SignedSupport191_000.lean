import SupportData191
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport191
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0282.C9028, NewCertificates0282.C9029, NewCertificates0282.C9030, NewCertificates0282.C9031, NewCertificates0282.C9032, NewCertificates0282.C9033, NewCertificates0282.C9034, NewCertificates0282.C9035, NewCertificates0282.C9036, NewCertificates0282.C9037, NewCertificates0282.C9038, NewCertificates0282.C9039, NewCertificates0282.C9040, NewCertificates0282.C9041, NewCertificates0282.C9042, NewCertificates0282.C9043, NewCertificates0282.C9044, NewCertificates0282.C9045, NewCertificates0282.C9046, NewCertificates0282.C9047, NewCertificates0282.C9048, NewCertificates0282.C9049, NewCertificates0282.C9050, NewCertificates0282.C9051, NewCertificates0282.C9052, NewCertificates0282.C9053, NewCertificates0282.C9054, NewCertificates0282.C9055, NewCertificates0283.C9056, NewCertificates0283.C9057, NewCertificates0283.C9058, NewCertificates0283.C9059} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0283.C9060, NewCertificates0283.C9061, NewCertificates0283.C9062, NewCertificates0283.C9063, NewCertificates0283.C9064, NewCertificates0283.C9065, NewCertificates0283.C9066, NewCertificates0283.C9067, NewCertificates0283.C9068, NewCertificates0283.C9069, NewCertificates0283.C9070, NewCertificates0283.C9071, NewCertificates0283.C9072, NewCertificates0283.C9073, NewCertificates0283.C9074, NewCertificates0283.C9075} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0282.obstruction9028
  · exact NewCertificates0282.obstruction9029
  · exact NewCertificates0282.obstruction9030
  · exact NewCertificates0282.obstruction9031
  · exact NewCertificates0282.obstruction9032
  · exact NewCertificates0282.obstruction9033
  · exact NewCertificates0282.obstruction9034
  · exact NewCertificates0282.obstruction9035
  · exact NewCertificates0282.obstruction9036
  · exact NewCertificates0282.obstruction9037
  · exact NewCertificates0282.obstruction9038
  · exact NewCertificates0282.obstruction9039
  · exact NewCertificates0282.obstruction9040
  · exact NewCertificates0282.obstruction9041
  · exact NewCertificates0282.obstruction9042
  · exact NewCertificates0282.obstruction9043
  · exact NewCertificates0282.obstruction9044
  · exact NewCertificates0282.obstruction9045
  · exact NewCertificates0282.obstruction9046
  · exact NewCertificates0282.obstruction9047
  · exact NewCertificates0282.obstruction9048
  · exact NewCertificates0282.obstruction9049
  · exact NewCertificates0282.obstruction9050
  · exact NewCertificates0282.obstruction9051
  · exact NewCertificates0282.obstruction9052
  · exact NewCertificates0282.obstruction9053
  · exact NewCertificates0282.obstruction9054
  · exact NewCertificates0282.obstruction9055
  · exact NewCertificates0283.obstruction9056
  · exact NewCertificates0283.obstruction9057
  · exact NewCertificates0283.obstruction9058
  · exact NewCertificates0283.obstruction9059
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0283.obstruction9060
  · exact NewCertificates0283.obstruction9061
  · exact NewCertificates0283.obstruction9062
  · exact NewCertificates0283.obstruction9063
  · exact NewCertificates0283.obstruction9064
  · exact NewCertificates0283.obstruction9065
  · exact NewCertificates0283.obstruction9066
  · exact NewCertificates0283.obstruction9067
  · exact NewCertificates0283.obstruction9068
  · exact NewCertificates0283.obstruction9069
  · exact NewCertificates0283.obstruction9070
  · exact NewCertificates0283.obstruction9071
  · exact NewCertificates0283.obstruction9072
  · exact NewCertificates0283.obstruction9073
  · exact NewCertificates0283.obstruction9074
  · exact NewCertificates0283.obstruction9075
end Nut8.FiniteSupport191
