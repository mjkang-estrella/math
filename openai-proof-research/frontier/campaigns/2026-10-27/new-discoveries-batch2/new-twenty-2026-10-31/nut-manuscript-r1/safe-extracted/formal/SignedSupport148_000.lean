import SupportData148
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport148
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0214.C6852, NewCertificates0214.C6853, NewCertificates0214.C6854, NewCertificates0214.C6855, NewCertificates0214.C6856, NewCertificates0214.C6857, NewCertificates0214.C6858, NewCertificates0214.C6859, NewCertificates0214.C6860, NewCertificates0214.C6861, NewCertificates0214.C6862, NewCertificates0214.C6863, NewCertificates0214.C6864, NewCertificates0214.C6865, NewCertificates0214.C6866, NewCertificates0214.C6867} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0214.C6868, NewCertificates0214.C6869, NewCertificates0214.C6870, NewCertificates0214.C6871, NewCertificates0214.C6872, NewCertificates0214.C6873, NewCertificates0214.C6874, NewCertificates0214.C6875, NewCertificates0214.C6876, NewCertificates0214.C6877, NewCertificates0214.C6878, NewCertificates0214.C6879, NewCertificates0215.C6880, NewCertificates0215.C6881, NewCertificates0215.C6882, NewCertificates0215.C6883} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0215.C6884, NewCertificates0215.C6885, NewCertificates0215.C6886, NewCertificates0215.C6887, NewCertificates0215.C6888, NewCertificates0215.C6889, NewCertificates0215.C6890, NewCertificates0215.C6891} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0215.C6892, NewCertificates0215.C6893, NewCertificates0215.C6894, NewCertificates0215.C6895, NewCertificates0215.C6896, NewCertificates0215.C6897, NewCertificates0215.C6898, NewCertificates0215.C6899} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0214.obstruction6852
  · exact NewCertificates0214.obstruction6853
  · exact NewCertificates0214.obstruction6854
  · exact NewCertificates0214.obstruction6855
  · exact NewCertificates0214.obstruction6856
  · exact NewCertificates0214.obstruction6857
  · exact NewCertificates0214.obstruction6858
  · exact NewCertificates0214.obstruction6859
  · exact NewCertificates0214.obstruction6860
  · exact NewCertificates0214.obstruction6861
  · exact NewCertificates0214.obstruction6862
  · exact NewCertificates0214.obstruction6863
  · exact NewCertificates0214.obstruction6864
  · exact NewCertificates0214.obstruction6865
  · exact NewCertificates0214.obstruction6866
  · exact NewCertificates0214.obstruction6867
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0214.obstruction6868
  · exact NewCertificates0214.obstruction6869
  · exact NewCertificates0214.obstruction6870
  · exact NewCertificates0214.obstruction6871
  · exact NewCertificates0214.obstruction6872
  · exact NewCertificates0214.obstruction6873
  · exact NewCertificates0214.obstruction6874
  · exact NewCertificates0214.obstruction6875
  · exact NewCertificates0214.obstruction6876
  · exact NewCertificates0214.obstruction6877
  · exact NewCertificates0214.obstruction6878
  · exact NewCertificates0214.obstruction6879
  · exact NewCertificates0215.obstruction6880
  · exact NewCertificates0215.obstruction6881
  · exact NewCertificates0215.obstruction6882
  · exact NewCertificates0215.obstruction6883
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0215.obstruction6884
  · exact NewCertificates0215.obstruction6885
  · exact NewCertificates0215.obstruction6886
  · exact NewCertificates0215.obstruction6887
  · exact NewCertificates0215.obstruction6888
  · exact NewCertificates0215.obstruction6889
  · exact NewCertificates0215.obstruction6890
  · exact NewCertificates0215.obstruction6891
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0215.obstruction6892
  · exact NewCertificates0215.obstruction6893
  · exact NewCertificates0215.obstruction6894
  · exact NewCertificates0215.obstruction6895
  · exact NewCertificates0215.obstruction6896
  · exact NewCertificates0215.obstruction6897
  · exact NewCertificates0215.obstruction6898
  · exact NewCertificates0215.obstruction6899
end Nut8.FiniteSupport148
