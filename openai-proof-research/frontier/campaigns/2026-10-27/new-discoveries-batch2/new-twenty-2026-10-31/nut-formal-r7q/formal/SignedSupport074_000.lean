import SupportData074
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport074
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0110.C3542, NewCertificates0110.C3543, NewCertificates0110.C3544, NewCertificates0110.C3545, NewCertificates0110.C3546, NewCertificates0110.C3547, NewCertificates0110.C3548, NewCertificates0110.C3549, NewCertificates0110.C3550, NewCertificates0110.C3551, NewCertificates0111.C3552, NewCertificates0111.C3553, NewCertificates0111.C3554, NewCertificates0111.C3555, NewCertificates0111.C3556, NewCertificates0111.C3557} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0111.C3558, NewCertificates0111.C3559, NewCertificates0111.C3560, NewCertificates0111.C3561, NewCertificates0111.C3562, NewCertificates0111.C3563, NewCertificates0111.C3564, NewCertificates0111.C3565, NewCertificates0111.C3566, NewCertificates0111.C3567, NewCertificates0111.C3568, NewCertificates0111.C3569, NewCertificates0111.C3570, NewCertificates0111.C3571, NewCertificates0111.C3572, NewCertificates0111.C3573} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0110.obstruction3542
  · exact NewCertificates0110.obstruction3543
  · exact NewCertificates0110.obstruction3544
  · exact NewCertificates0110.obstruction3545
  · exact NewCertificates0110.obstruction3546
  · exact NewCertificates0110.obstruction3547
  · exact NewCertificates0110.obstruction3548
  · exact NewCertificates0110.obstruction3549
  · exact NewCertificates0110.obstruction3550
  · exact NewCertificates0110.obstruction3551
  · exact NewCertificates0111.obstruction3552
  · exact NewCertificates0111.obstruction3553
  · exact NewCertificates0111.obstruction3554
  · exact NewCertificates0111.obstruction3555
  · exact NewCertificates0111.obstruction3556
  · exact NewCertificates0111.obstruction3557
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0111.obstruction3558
  · exact NewCertificates0111.obstruction3559
  · exact NewCertificates0111.obstruction3560
  · exact NewCertificates0111.obstruction3561
  · exact NewCertificates0111.obstruction3562
  · exact NewCertificates0111.obstruction3563
  · exact NewCertificates0111.obstruction3564
  · exact NewCertificates0111.obstruction3565
  · exact NewCertificates0111.obstruction3566
  · exact NewCertificates0111.obstruction3567
  · exact NewCertificates0111.obstruction3568
  · exact NewCertificates0111.obstruction3569
  · exact NewCertificates0111.obstruction3570
  · exact NewCertificates0111.obstruction3571
  · exact NewCertificates0111.obstruction3572
  · exact NewCertificates0111.obstruction3573
end Nut8.FiniteSupport074
