import SupportData136
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport136
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0199.C6388, NewCertificates0199.C6389, NewCertificates0199.C6390, NewCertificates0199.C6391, NewCertificates0199.C6392, NewCertificates0199.C6393, NewCertificates0199.C6394, NewCertificates0199.C6395, NewCertificates0199.C6396, NewCertificates0199.C6397, NewCertificates0199.C6398, NewCertificates0199.C6399, NewCertificates0200.C6400, NewCertificates0200.C6401, NewCertificates0200.C6402, NewCertificates0200.C6403} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0200.C6404, NewCertificates0200.C6405, NewCertificates0200.C6406, NewCertificates0200.C6407, NewCertificates0200.C6408, NewCertificates0200.C6409, NewCertificates0200.C6410, NewCertificates0200.C6411, NewCertificates0200.C6412, NewCertificates0200.C6413, NewCertificates0200.C6414, NewCertificates0200.C6415, NewCertificates0200.C6416, NewCertificates0200.C6417, NewCertificates0200.C6418, NewCertificates0200.C6419} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0199.obstruction6388
  · exact NewCertificates0199.obstruction6389
  · exact NewCertificates0199.obstruction6390
  · exact NewCertificates0199.obstruction6391
  · exact NewCertificates0199.obstruction6392
  · exact NewCertificates0199.obstruction6393
  · exact NewCertificates0199.obstruction6394
  · exact NewCertificates0199.obstruction6395
  · exact NewCertificates0199.obstruction6396
  · exact NewCertificates0199.obstruction6397
  · exact NewCertificates0199.obstruction6398
  · exact NewCertificates0199.obstruction6399
  · exact NewCertificates0200.obstruction6400
  · exact NewCertificates0200.obstruction6401
  · exact NewCertificates0200.obstruction6402
  · exact NewCertificates0200.obstruction6403
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0200.obstruction6404
  · exact NewCertificates0200.obstruction6405
  · exact NewCertificates0200.obstruction6406
  · exact NewCertificates0200.obstruction6407
  · exact NewCertificates0200.obstruction6408
  · exact NewCertificates0200.obstruction6409
  · exact NewCertificates0200.obstruction6410
  · exact NewCertificates0200.obstruction6411
  · exact NewCertificates0200.obstruction6412
  · exact NewCertificates0200.obstruction6413
  · exact NewCertificates0200.obstruction6414
  · exact NewCertificates0200.obstruction6415
  · exact NewCertificates0200.obstruction6416
  · exact NewCertificates0200.obstruction6417
  · exact NewCertificates0200.obstruction6418
  · exact NewCertificates0200.obstruction6419
end Nut8.FiniteSupport136
