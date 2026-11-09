import SupportData085
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport085
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0122.C3926, NewCertificates0122.C3927, NewCertificates0122.C3928, NewCertificates0122.C3929, NewCertificates0122.C3930, NewCertificates0122.C3931, NewCertificates0122.C3932, NewCertificates0122.C3933, NewCertificates0122.C3934, NewCertificates0122.C3935, NewCertificates0123.C3936, NewCertificates0123.C3937, NewCertificates0123.C3938, NewCertificates0123.C3939, NewCertificates0123.C3940, NewCertificates0123.C3941, NewCertificates0123.C3942, NewCertificates0123.C3943, NewCertificates0123.C3944, NewCertificates0123.C3945, NewCertificates0123.C3946, NewCertificates0123.C3947, NewCertificates0123.C3948, NewCertificates0123.C3949, NewCertificates0123.C3950, NewCertificates0123.C3951, NewCertificates0123.C3952, NewCertificates0123.C3953, NewCertificates0123.C3954, NewCertificates0123.C3955, NewCertificates0123.C3956, NewCertificates0123.C3957} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0122.obstruction3926
  · exact NewCertificates0122.obstruction3927
  · exact NewCertificates0122.obstruction3928
  · exact NewCertificates0122.obstruction3929
  · exact NewCertificates0122.obstruction3930
  · exact NewCertificates0122.obstruction3931
  · exact NewCertificates0122.obstruction3932
  · exact NewCertificates0122.obstruction3933
  · exact NewCertificates0122.obstruction3934
  · exact NewCertificates0122.obstruction3935
  · exact NewCertificates0123.obstruction3936
  · exact NewCertificates0123.obstruction3937
  · exact NewCertificates0123.obstruction3938
  · exact NewCertificates0123.obstruction3939
  · exact NewCertificates0123.obstruction3940
  · exact NewCertificates0123.obstruction3941
  · exact NewCertificates0123.obstruction3942
  · exact NewCertificates0123.obstruction3943
  · exact NewCertificates0123.obstruction3944
  · exact NewCertificates0123.obstruction3945
  · exact NewCertificates0123.obstruction3946
  · exact NewCertificates0123.obstruction3947
  · exact NewCertificates0123.obstruction3948
  · exact NewCertificates0123.obstruction3949
  · exact NewCertificates0123.obstruction3950
  · exact NewCertificates0123.obstruction3951
  · exact NewCertificates0123.obstruction3952
  · exact NewCertificates0123.obstruction3953
  · exact NewCertificates0123.obstruction3954
  · exact NewCertificates0123.obstruction3955
  · exact NewCertificates0123.obstruction3956
  · exact NewCertificates0123.obstruction3957
end Nut8.FiniteSupport085
