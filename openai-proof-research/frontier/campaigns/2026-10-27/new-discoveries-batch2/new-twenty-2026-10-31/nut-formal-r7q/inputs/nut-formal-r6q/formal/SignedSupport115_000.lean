import SupportData115
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport115
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0173.C5564, NewCertificates0173.C5565, NewCertificates0173.C5566, NewCertificates0173.C5567, NewCertificates0174.C5568, NewCertificates0174.C5569, NewCertificates0174.C5570, NewCertificates0174.C5571, NewCertificates0174.C5572, NewCertificates0174.C5573, NewCertificates0174.C5574, NewCertificates0174.C5575, NewCertificates0174.C5576, NewCertificates0174.C5577, NewCertificates0174.C5578, NewCertificates0174.C5579} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0173.obstruction5564
  · exact NewCertificates0173.obstruction5565
  · exact NewCertificates0173.obstruction5566
  · exact NewCertificates0173.obstruction5567
  · exact NewCertificates0174.obstruction5568
  · exact NewCertificates0174.obstruction5569
  · exact NewCertificates0174.obstruction5570
  · exact NewCertificates0174.obstruction5571
  · exact NewCertificates0174.obstruction5572
  · exact NewCertificates0174.obstruction5573
  · exact NewCertificates0174.obstruction5574
  · exact NewCertificates0174.obstruction5575
  · exact NewCertificates0174.obstruction5576
  · exact NewCertificates0174.obstruction5577
  · exact NewCertificates0174.obstruction5578
  · exact NewCertificates0174.obstruction5579
end Nut8.FiniteSupport115
