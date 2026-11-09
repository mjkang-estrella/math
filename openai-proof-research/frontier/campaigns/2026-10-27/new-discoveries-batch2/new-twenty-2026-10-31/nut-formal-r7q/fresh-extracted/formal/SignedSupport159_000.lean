import SupportData159
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport159
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0234.C7508, NewCertificates0234.C7509, NewCertificates0234.C7510, NewCertificates0234.C7511, NewCertificates0234.C7512, NewCertificates0234.C7513, NewCertificates0234.C7514, NewCertificates0234.C7515, NewCertificates0234.C7516, NewCertificates0234.C7517, NewCertificates0234.C7518, NewCertificates0234.C7519, NewCertificates0235.C7520, NewCertificates0235.C7521, NewCertificates0235.C7522, NewCertificates0235.C7523} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0235.C7524, NewCertificates0235.C7525, NewCertificates0235.C7526, NewCertificates0235.C7527, NewCertificates0235.C7528, NewCertificates0235.C7529, NewCertificates0235.C7530, NewCertificates0235.C7531, NewCertificates0235.C7532, NewCertificates0235.C7533, NewCertificates0235.C7534, NewCertificates0235.C7535, NewCertificates0235.C7536, NewCertificates0235.C7537, NewCertificates0235.C7538, NewCertificates0235.C7539} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0234.obstruction7508
  · exact NewCertificates0234.obstruction7509
  · exact NewCertificates0234.obstruction7510
  · exact NewCertificates0234.obstruction7511
  · exact NewCertificates0234.obstruction7512
  · exact NewCertificates0234.obstruction7513
  · exact NewCertificates0234.obstruction7514
  · exact NewCertificates0234.obstruction7515
  · exact NewCertificates0234.obstruction7516
  · exact NewCertificates0234.obstruction7517
  · exact NewCertificates0234.obstruction7518
  · exact NewCertificates0234.obstruction7519
  · exact NewCertificates0235.obstruction7520
  · exact NewCertificates0235.obstruction7521
  · exact NewCertificates0235.obstruction7522
  · exact NewCertificates0235.obstruction7523
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0235.obstruction7524
  · exact NewCertificates0235.obstruction7525
  · exact NewCertificates0235.obstruction7526
  · exact NewCertificates0235.obstruction7527
  · exact NewCertificates0235.obstruction7528
  · exact NewCertificates0235.obstruction7529
  · exact NewCertificates0235.obstruction7530
  · exact NewCertificates0235.obstruction7531
  · exact NewCertificates0235.obstruction7532
  · exact NewCertificates0235.obstruction7533
  · exact NewCertificates0235.obstruction7534
  · exact NewCertificates0235.obstruction7535
  · exact NewCertificates0235.obstruction7536
  · exact NewCertificates0235.obstruction7537
  · exact NewCertificates0235.obstruction7538
  · exact NewCertificates0235.obstruction7539
end Nut8.FiniteSupport159
