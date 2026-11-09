import SupportData188
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport188
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0277.C8876, NewCertificates0277.C8877, NewCertificates0277.C8878, NewCertificates0277.C8879, NewCertificates0277.C8880, NewCertificates0277.C8881, NewCertificates0277.C8882, NewCertificates0277.C8883, NewCertificates0277.C8884, NewCertificates0277.C8885, NewCertificates0277.C8886, NewCertificates0277.C8887, NewCertificates0277.C8888, NewCertificates0277.C8889, NewCertificates0277.C8890, NewCertificates0277.C8891, NewCertificates0277.C8892, NewCertificates0277.C8893, NewCertificates0277.C8894, NewCertificates0277.C8895, NewCertificates0278.C8896, NewCertificates0278.C8897, NewCertificates0278.C8898, NewCertificates0278.C8899, NewCertificates0278.C8900, NewCertificates0278.C8901, NewCertificates0278.C8902, NewCertificates0278.C8903, NewCertificates0278.C8904, NewCertificates0278.C8905, NewCertificates0278.C8906, NewCertificates0278.C8907} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0278.C8908, NewCertificates0278.C8909, NewCertificates0278.C8910, NewCertificates0278.C8911, NewCertificates0278.C8912, NewCertificates0278.C8913, NewCertificates0278.C8914, NewCertificates0278.C8915, NewCertificates0278.C8916, NewCertificates0278.C8917, NewCertificates0278.C8918, NewCertificates0278.C8919, NewCertificates0278.C8920, NewCertificates0278.C8921, NewCertificates0278.C8922, NewCertificates0278.C8923} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0277.obstruction8876
  · exact NewCertificates0277.obstruction8877
  · exact NewCertificates0277.obstruction8878
  · exact NewCertificates0277.obstruction8879
  · exact NewCertificates0277.obstruction8880
  · exact NewCertificates0277.obstruction8881
  · exact NewCertificates0277.obstruction8882
  · exact NewCertificates0277.obstruction8883
  · exact NewCertificates0277.obstruction8884
  · exact NewCertificates0277.obstruction8885
  · exact NewCertificates0277.obstruction8886
  · exact NewCertificates0277.obstruction8887
  · exact NewCertificates0277.obstruction8888
  · exact NewCertificates0277.obstruction8889
  · exact NewCertificates0277.obstruction8890
  · exact NewCertificates0277.obstruction8891
  · exact NewCertificates0277.obstruction8892
  · exact NewCertificates0277.obstruction8893
  · exact NewCertificates0277.obstruction8894
  · exact NewCertificates0277.obstruction8895
  · exact NewCertificates0278.obstruction8896
  · exact NewCertificates0278.obstruction8897
  · exact NewCertificates0278.obstruction8898
  · exact NewCertificates0278.obstruction8899
  · exact NewCertificates0278.obstruction8900
  · exact NewCertificates0278.obstruction8901
  · exact NewCertificates0278.obstruction8902
  · exact NewCertificates0278.obstruction8903
  · exact NewCertificates0278.obstruction8904
  · exact NewCertificates0278.obstruction8905
  · exact NewCertificates0278.obstruction8906
  · exact NewCertificates0278.obstruction8907
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0278.obstruction8908
  · exact NewCertificates0278.obstruction8909
  · exact NewCertificates0278.obstruction8910
  · exact NewCertificates0278.obstruction8911
  · exact NewCertificates0278.obstruction8912
  · exact NewCertificates0278.obstruction8913
  · exact NewCertificates0278.obstruction8914
  · exact NewCertificates0278.obstruction8915
  · exact NewCertificates0278.obstruction8916
  · exact NewCertificates0278.obstruction8917
  · exact NewCertificates0278.obstruction8918
  · exact NewCertificates0278.obstruction8919
  · exact NewCertificates0278.obstruction8920
  · exact NewCertificates0278.obstruction8921
  · exact NewCertificates0278.obstruction8922
  · exact NewCertificates0278.obstruction8923
end Nut8.FiniteSupport188
