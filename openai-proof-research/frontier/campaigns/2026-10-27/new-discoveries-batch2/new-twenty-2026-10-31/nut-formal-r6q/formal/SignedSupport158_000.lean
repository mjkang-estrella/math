import SupportData158
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport158
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0233.C7476, NewCertificates0233.C7477, NewCertificates0233.C7478, NewCertificates0233.C7479, NewCertificates0233.C7480, NewCertificates0233.C7481, NewCertificates0233.C7482, NewCertificates0233.C7483, NewCertificates0233.C7484, NewCertificates0233.C7485, NewCertificates0233.C7486, NewCertificates0233.C7487, NewCertificates0234.C7488, NewCertificates0234.C7489, NewCertificates0234.C7490, NewCertificates0234.C7491} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0234.C7492, NewCertificates0234.C7493, NewCertificates0234.C7494, NewCertificates0234.C7495, NewCertificates0234.C7496, NewCertificates0234.C7497, NewCertificates0234.C7498, NewCertificates0234.C7499, NewCertificates0234.C7500, NewCertificates0234.C7501, NewCertificates0234.C7502, NewCertificates0234.C7503, NewCertificates0234.C7504, NewCertificates0234.C7505, NewCertificates0234.C7506, NewCertificates0234.C7507} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0233.obstruction7476
  · exact NewCertificates0233.obstruction7477
  · exact NewCertificates0233.obstruction7478
  · exact NewCertificates0233.obstruction7479
  · exact NewCertificates0233.obstruction7480
  · exact NewCertificates0233.obstruction7481
  · exact NewCertificates0233.obstruction7482
  · exact NewCertificates0233.obstruction7483
  · exact NewCertificates0233.obstruction7484
  · exact NewCertificates0233.obstruction7485
  · exact NewCertificates0233.obstruction7486
  · exact NewCertificates0233.obstruction7487
  · exact NewCertificates0234.obstruction7488
  · exact NewCertificates0234.obstruction7489
  · exact NewCertificates0234.obstruction7490
  · exact NewCertificates0234.obstruction7491
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0234.obstruction7492
  · exact NewCertificates0234.obstruction7493
  · exact NewCertificates0234.obstruction7494
  · exact NewCertificates0234.obstruction7495
  · exact NewCertificates0234.obstruction7496
  · exact NewCertificates0234.obstruction7497
  · exact NewCertificates0234.obstruction7498
  · exact NewCertificates0234.obstruction7499
  · exact NewCertificates0234.obstruction7500
  · exact NewCertificates0234.obstruction7501
  · exact NewCertificates0234.obstruction7502
  · exact NewCertificates0234.obstruction7503
  · exact NewCertificates0234.obstruction7504
  · exact NewCertificates0234.obstruction7505
  · exact NewCertificates0234.obstruction7506
  · exact NewCertificates0234.obstruction7507
end Nut8.FiniteSupport158
