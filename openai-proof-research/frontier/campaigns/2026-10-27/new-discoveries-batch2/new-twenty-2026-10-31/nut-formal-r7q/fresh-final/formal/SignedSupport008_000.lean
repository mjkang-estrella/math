import SupportData008
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport008
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0012.C384, NewCertificates0012.C385, NewCertificates0012.C386, NewCertificates0012.C387, NewCertificates0012.C388, NewCertificates0012.C389, NewCertificates0012.C390, NewCertificates0012.C391, NewCertificates0012.C392, NewCertificates0012.C393, NewCertificates0012.C394, NewCertificates0012.C395, NewCertificates0012.C396, NewCertificates0012.C397, NewCertificates0012.C398, NewCertificates0012.C399, NewCertificates0012.C400, NewCertificates0012.C401, NewCertificates0012.C402, NewCertificates0012.C403, NewCertificates0012.C404, NewCertificates0012.C405, NewCertificates0012.C406, NewCertificates0012.C407, NewCertificates0012.C408, NewCertificates0012.C409, NewCertificates0012.C410, NewCertificates0012.C411, NewCertificates0012.C412, NewCertificates0012.C413, NewCertificates0012.C414, NewCertificates0012.C415} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0013.C416, NewCertificates0013.C417, NewCertificates0013.C418, NewCertificates0013.C419, NewCertificates0013.C420, NewCertificates0013.C421, NewCertificates0013.C422, NewCertificates0013.C423, NewCertificates0013.C424, NewCertificates0013.C425, NewCertificates0013.C426, NewCertificates0013.C427, NewCertificates0013.C428, NewCertificates0013.C429, NewCertificates0013.C430, NewCertificates0013.C431} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0012.obstruction384
  · exact NewCertificates0012.obstruction385
  · exact NewCertificates0012.obstruction386
  · exact NewCertificates0012.obstruction387
  · exact NewCertificates0012.obstruction388
  · exact NewCertificates0012.obstruction389
  · exact NewCertificates0012.obstruction390
  · exact NewCertificates0012.obstruction391
  · exact NewCertificates0012.obstruction392
  · exact NewCertificates0012.obstruction393
  · exact NewCertificates0012.obstruction394
  · exact NewCertificates0012.obstruction395
  · exact NewCertificates0012.obstruction396
  · exact NewCertificates0012.obstruction397
  · exact NewCertificates0012.obstruction398
  · exact NewCertificates0012.obstruction399
  · exact NewCertificates0012.obstruction400
  · exact NewCertificates0012.obstruction401
  · exact NewCertificates0012.obstruction402
  · exact NewCertificates0012.obstruction403
  · exact NewCertificates0012.obstruction404
  · exact NewCertificates0012.obstruction405
  · exact NewCertificates0012.obstruction406
  · exact NewCertificates0012.obstruction407
  · exact NewCertificates0012.obstruction408
  · exact NewCertificates0012.obstruction409
  · exact NewCertificates0012.obstruction410
  · exact NewCertificates0012.obstruction411
  · exact NewCertificates0012.obstruction412
  · exact NewCertificates0012.obstruction413
  · exact NewCertificates0012.obstruction414
  · exact NewCertificates0012.obstruction415
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0013.obstruction416
  · exact NewCertificates0013.obstruction417
  · exact NewCertificates0013.obstruction418
  · exact NewCertificates0013.obstruction419
  · exact NewCertificates0013.obstruction420
  · exact NewCertificates0013.obstruction421
  · exact NewCertificates0013.obstruction422
  · exact NewCertificates0013.obstruction423
  · exact NewCertificates0013.obstruction424
  · exact NewCertificates0013.obstruction425
  · exact NewCertificates0013.obstruction426
  · exact NewCertificates0013.obstruction427
  · exact NewCertificates0013.obstruction428
  · exact NewCertificates0013.obstruction429
  · exact NewCertificates0013.obstruction430
  · exact NewCertificates0013.obstruction431
end Nut8.FiniteSupport008
