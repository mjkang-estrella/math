import SupportData019
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport019
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0027.C888, NewCertificates0027.C889, NewCertificates0027.C890, NewCertificates0027.C891, NewCertificates0027.C892, NewCertificates0027.C893, NewCertificates0027.C894, NewCertificates0027.C895, NewCertificates0028.C896, NewCertificates0028.C897, NewCertificates0028.C898, NewCertificates0028.C899, NewCertificates0028.C900, NewCertificates0028.C901, NewCertificates0028.C902, NewCertificates0028.C903, NewCertificates0028.C904, NewCertificates0028.C905, NewCertificates0028.C906, NewCertificates0028.C907, NewCertificates0028.C908, NewCertificates0028.C909, NewCertificates0028.C910, NewCertificates0028.C911, NewCertificates0028.C912, NewCertificates0028.C913, NewCertificates0028.C914, NewCertificates0028.C915, NewCertificates0028.C916, NewCertificates0028.C917, NewCertificates0028.C918, NewCertificates0028.C919} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0028.C920, NewCertificates0028.C921, NewCertificates0028.C922, NewCertificates0028.C923, NewCertificates0028.C924, NewCertificates0028.C925, NewCertificates0028.C926, NewCertificates0028.C927, NewCertificates0029.C928, NewCertificates0029.C929, NewCertificates0029.C930, NewCertificates0029.C931, NewCertificates0029.C932, NewCertificates0029.C933, NewCertificates0029.C934, NewCertificates0029.C935} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0027.obstruction888
  · exact NewCertificates0027.obstruction889
  · exact NewCertificates0027.obstruction890
  · exact NewCertificates0027.obstruction891
  · exact NewCertificates0027.obstruction892
  · exact NewCertificates0027.obstruction893
  · exact NewCertificates0027.obstruction894
  · exact NewCertificates0027.obstruction895
  · exact NewCertificates0028.obstruction896
  · exact NewCertificates0028.obstruction897
  · exact NewCertificates0028.obstruction898
  · exact NewCertificates0028.obstruction899
  · exact NewCertificates0028.obstruction900
  · exact NewCertificates0028.obstruction901
  · exact NewCertificates0028.obstruction902
  · exact NewCertificates0028.obstruction903
  · exact NewCertificates0028.obstruction904
  · exact NewCertificates0028.obstruction905
  · exact NewCertificates0028.obstruction906
  · exact NewCertificates0028.obstruction907
  · exact NewCertificates0028.obstruction908
  · exact NewCertificates0028.obstruction909
  · exact NewCertificates0028.obstruction910
  · exact NewCertificates0028.obstruction911
  · exact NewCertificates0028.obstruction912
  · exact NewCertificates0028.obstruction913
  · exact NewCertificates0028.obstruction914
  · exact NewCertificates0028.obstruction915
  · exact NewCertificates0028.obstruction916
  · exact NewCertificates0028.obstruction917
  · exact NewCertificates0028.obstruction918
  · exact NewCertificates0028.obstruction919
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0028.obstruction920
  · exact NewCertificates0028.obstruction921
  · exact NewCertificates0028.obstruction922
  · exact NewCertificates0028.obstruction923
  · exact NewCertificates0028.obstruction924
  · exact NewCertificates0028.obstruction925
  · exact NewCertificates0028.obstruction926
  · exact NewCertificates0028.obstruction927
  · exact NewCertificates0029.obstruction928
  · exact NewCertificates0029.obstruction929
  · exact NewCertificates0029.obstruction930
  · exact NewCertificates0029.obstruction931
  · exact NewCertificates0029.obstruction932
  · exact NewCertificates0029.obstruction933
  · exact NewCertificates0029.obstruction934
  · exact NewCertificates0029.obstruction935
end Nut8.FiniteSupport019
