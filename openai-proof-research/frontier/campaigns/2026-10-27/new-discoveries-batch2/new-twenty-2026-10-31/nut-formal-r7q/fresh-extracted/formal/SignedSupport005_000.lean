import SupportData005
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport005
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0007.C224, NewCertificates0007.C225, NewCertificates0007.C226, NewCertificates0007.C227, NewCertificates0007.C228, NewCertificates0007.C229, NewCertificates0007.C230, NewCertificates0007.C231, NewCertificates0007.C232, NewCertificates0007.C233, NewCertificates0007.C234, NewCertificates0007.C235, NewCertificates0007.C236, NewCertificates0007.C237, NewCertificates0007.C238, NewCertificates0007.C239} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0007.C240, NewCertificates0007.C241, NewCertificates0007.C242, NewCertificates0007.C243, NewCertificates0007.C244, NewCertificates0007.C245, NewCertificates0007.C246, NewCertificates0007.C247} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0007.C248, NewCertificates0007.C249, NewCertificates0007.C250, NewCertificates0007.C251, NewCertificates0007.C252, NewCertificates0007.C253, NewCertificates0007.C254, NewCertificates0007.C255, NewCertificates0008.C256, NewCertificates0008.C257, NewCertificates0008.C258, NewCertificates0008.C259, NewCertificates0008.C260, NewCertificates0008.C261, NewCertificates0008.C262, NewCertificates0008.C263} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0008.C264, NewCertificates0008.C265, NewCertificates0008.C266, NewCertificates0008.C267, NewCertificates0008.C268, NewCertificates0008.C269, NewCertificates0008.C270, NewCertificates0008.C271, NewCertificates0008.C272, NewCertificates0008.C273, NewCertificates0008.C274, NewCertificates0008.C275, NewCertificates0008.C276, NewCertificates0008.C277, NewCertificates0008.C278, NewCertificates0008.C279} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0007.obstruction224
  · exact NewCertificates0007.obstruction225
  · exact NewCertificates0007.obstruction226
  · exact NewCertificates0007.obstruction227
  · exact NewCertificates0007.obstruction228
  · exact NewCertificates0007.obstruction229
  · exact NewCertificates0007.obstruction230
  · exact NewCertificates0007.obstruction231
  · exact NewCertificates0007.obstruction232
  · exact NewCertificates0007.obstruction233
  · exact NewCertificates0007.obstruction234
  · exact NewCertificates0007.obstruction235
  · exact NewCertificates0007.obstruction236
  · exact NewCertificates0007.obstruction237
  · exact NewCertificates0007.obstruction238
  · exact NewCertificates0007.obstruction239
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0007.obstruction240
  · exact NewCertificates0007.obstruction241
  · exact NewCertificates0007.obstruction242
  · exact NewCertificates0007.obstruction243
  · exact NewCertificates0007.obstruction244
  · exact NewCertificates0007.obstruction245
  · exact NewCertificates0007.obstruction246
  · exact NewCertificates0007.obstruction247
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0007.obstruction248
  · exact NewCertificates0007.obstruction249
  · exact NewCertificates0007.obstruction250
  · exact NewCertificates0007.obstruction251
  · exact NewCertificates0007.obstruction252
  · exact NewCertificates0007.obstruction253
  · exact NewCertificates0007.obstruction254
  · exact NewCertificates0007.obstruction255
  · exact NewCertificates0008.obstruction256
  · exact NewCertificates0008.obstruction257
  · exact NewCertificates0008.obstruction258
  · exact NewCertificates0008.obstruction259
  · exact NewCertificates0008.obstruction260
  · exact NewCertificates0008.obstruction261
  · exact NewCertificates0008.obstruction262
  · exact NewCertificates0008.obstruction263
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0008.obstruction264
  · exact NewCertificates0008.obstruction265
  · exact NewCertificates0008.obstruction266
  · exact NewCertificates0008.obstruction267
  · exact NewCertificates0008.obstruction268
  · exact NewCertificates0008.obstruction269
  · exact NewCertificates0008.obstruction270
  · exact NewCertificates0008.obstruction271
  · exact NewCertificates0008.obstruction272
  · exact NewCertificates0008.obstruction273
  · exact NewCertificates0008.obstruction274
  · exact NewCertificates0008.obstruction275
  · exact NewCertificates0008.obstruction276
  · exact NewCertificates0008.obstruction277
  · exact NewCertificates0008.obstruction278
  · exact NewCertificates0008.obstruction279
end Nut8.FiniteSupport005
