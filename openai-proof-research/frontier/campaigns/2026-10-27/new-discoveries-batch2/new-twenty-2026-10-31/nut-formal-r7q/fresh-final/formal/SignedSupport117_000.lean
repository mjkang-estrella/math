import SupportData117
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport117
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0175.C5612, NewCertificates0175.C5613, NewCertificates0175.C5614, NewCertificates0175.C5615, NewCertificates0175.C5616, NewCertificates0175.C5617, NewCertificates0175.C5618, NewCertificates0175.C5619, NewCertificates0175.C5620, NewCertificates0175.C5621, NewCertificates0175.C5622, NewCertificates0175.C5623, NewCertificates0175.C5624, NewCertificates0175.C5625, NewCertificates0175.C5626, NewCertificates0175.C5627} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0175.C5628, NewCertificates0175.C5629, NewCertificates0175.C5630, NewCertificates0175.C5631, NewCertificates0176.C5632, NewCertificates0176.C5633, NewCertificates0176.C5634, NewCertificates0176.C5635, NewCertificates0176.C5636, NewCertificates0176.C5637, NewCertificates0176.C5638, NewCertificates0176.C5639, NewCertificates0176.C5640, NewCertificates0176.C5641, NewCertificates0176.C5642, NewCertificates0176.C5643} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0175.obstruction5612
  · exact NewCertificates0175.obstruction5613
  · exact NewCertificates0175.obstruction5614
  · exact NewCertificates0175.obstruction5615
  · exact NewCertificates0175.obstruction5616
  · exact NewCertificates0175.obstruction5617
  · exact NewCertificates0175.obstruction5618
  · exact NewCertificates0175.obstruction5619
  · exact NewCertificates0175.obstruction5620
  · exact NewCertificates0175.obstruction5621
  · exact NewCertificates0175.obstruction5622
  · exact NewCertificates0175.obstruction5623
  · exact NewCertificates0175.obstruction5624
  · exact NewCertificates0175.obstruction5625
  · exact NewCertificates0175.obstruction5626
  · exact NewCertificates0175.obstruction5627
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0175.obstruction5628
  · exact NewCertificates0175.obstruction5629
  · exact NewCertificates0175.obstruction5630
  · exact NewCertificates0175.obstruction5631
  · exact NewCertificates0176.obstruction5632
  · exact NewCertificates0176.obstruction5633
  · exact NewCertificates0176.obstruction5634
  · exact NewCertificates0176.obstruction5635
  · exact NewCertificates0176.obstruction5636
  · exact NewCertificates0176.obstruction5637
  · exact NewCertificates0176.obstruction5638
  · exact NewCertificates0176.obstruction5639
  · exact NewCertificates0176.obstruction5640
  · exact NewCertificates0176.obstruction5641
  · exact NewCertificates0176.obstruction5642
  · exact NewCertificates0176.obstruction5643
end Nut8.FiniteSupport117
