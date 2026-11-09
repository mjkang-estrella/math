import SupportData170
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport170
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0245.C7868, NewCertificates0245.C7869, NewCertificates0245.C7870, NewCertificates0245.C7871, NewCertificates0246.C7872, NewCertificates0246.C7873, NewCertificates0246.C7874, NewCertificates0246.C7875, NewCertificates0246.C7876, NewCertificates0246.C7877, NewCertificates0246.C7878, NewCertificates0246.C7879, NewCertificates0246.C7880, NewCertificates0246.C7881, NewCertificates0246.C7882, NewCertificates0246.C7883} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0246.C7884, NewCertificates0246.C7885, NewCertificates0246.C7886, NewCertificates0246.C7887, NewCertificates0246.C7888, NewCertificates0246.C7889, NewCertificates0246.C7890, NewCertificates0246.C7891, NewCertificates0246.C7892, NewCertificates0246.C7893, NewCertificates0246.C7894, NewCertificates0246.C7895, NewCertificates0246.C7896, NewCertificates0246.C7897, NewCertificates0246.C7898, NewCertificates0246.C7899} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0246.C7900, NewCertificates0246.C7901, NewCertificates0246.C7902, NewCertificates0246.C7903, NewCertificates0247.C7904, NewCertificates0247.C7905, NewCertificates0247.C7906, NewCertificates0247.C7907} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0245.obstruction7868
  · exact NewCertificates0245.obstruction7869
  · exact NewCertificates0245.obstruction7870
  · exact NewCertificates0245.obstruction7871
  · exact NewCertificates0246.obstruction7872
  · exact NewCertificates0246.obstruction7873
  · exact NewCertificates0246.obstruction7874
  · exact NewCertificates0246.obstruction7875
  · exact NewCertificates0246.obstruction7876
  · exact NewCertificates0246.obstruction7877
  · exact NewCertificates0246.obstruction7878
  · exact NewCertificates0246.obstruction7879
  · exact NewCertificates0246.obstruction7880
  · exact NewCertificates0246.obstruction7881
  · exact NewCertificates0246.obstruction7882
  · exact NewCertificates0246.obstruction7883
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0246.obstruction7884
  · exact NewCertificates0246.obstruction7885
  · exact NewCertificates0246.obstruction7886
  · exact NewCertificates0246.obstruction7887
  · exact NewCertificates0246.obstruction7888
  · exact NewCertificates0246.obstruction7889
  · exact NewCertificates0246.obstruction7890
  · exact NewCertificates0246.obstruction7891
  · exact NewCertificates0246.obstruction7892
  · exact NewCertificates0246.obstruction7893
  · exact NewCertificates0246.obstruction7894
  · exact NewCertificates0246.obstruction7895
  · exact NewCertificates0246.obstruction7896
  · exact NewCertificates0246.obstruction7897
  · exact NewCertificates0246.obstruction7898
  · exact NewCertificates0246.obstruction7899
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0246.obstruction7900
  · exact NewCertificates0246.obstruction7901
  · exact NewCertificates0246.obstruction7902
  · exact NewCertificates0246.obstruction7903
  · exact NewCertificates0247.obstruction7904
  · exact NewCertificates0247.obstruction7905
  · exact NewCertificates0247.obstruction7906
  · exact NewCertificates0247.obstruction7907
end Nut8.FiniteSupport170
