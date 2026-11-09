import SupportData143
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport143
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0206.C6612, NewCertificates0206.C6613, NewCertificates0206.C6614, NewCertificates0206.C6615, NewCertificates0206.C6616, NewCertificates0206.C6617, NewCertificates0206.C6618, NewCertificates0206.C6619, NewCertificates0206.C6620, NewCertificates0206.C6621, NewCertificates0206.C6622, NewCertificates0206.C6623, NewCertificates0207.C6624, NewCertificates0207.C6625, NewCertificates0207.C6626, NewCertificates0207.C6627} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0207.C6628, NewCertificates0207.C6629, NewCertificates0207.C6630, NewCertificates0207.C6631, NewCertificates0207.C6632, NewCertificates0207.C6633, NewCertificates0207.C6634, NewCertificates0207.C6635, NewCertificates0207.C6636, NewCertificates0207.C6637, NewCertificates0207.C6638, NewCertificates0207.C6639, NewCertificates0207.C6640, NewCertificates0207.C6641, NewCertificates0207.C6642, NewCertificates0207.C6643} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0207.C6644, NewCertificates0207.C6645, NewCertificates0207.C6646, NewCertificates0207.C6647, NewCertificates0207.C6648, NewCertificates0207.C6649, NewCertificates0207.C6650, NewCertificates0207.C6651, NewCertificates0207.C6652, NewCertificates0207.C6653, NewCertificates0207.C6654, NewCertificates0207.C6655, NewCertificates0208.C6656, NewCertificates0208.C6657, NewCertificates0208.C6658, NewCertificates0208.C6659} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0206.obstruction6612
  · exact NewCertificates0206.obstruction6613
  · exact NewCertificates0206.obstruction6614
  · exact NewCertificates0206.obstruction6615
  · exact NewCertificates0206.obstruction6616
  · exact NewCertificates0206.obstruction6617
  · exact NewCertificates0206.obstruction6618
  · exact NewCertificates0206.obstruction6619
  · exact NewCertificates0206.obstruction6620
  · exact NewCertificates0206.obstruction6621
  · exact NewCertificates0206.obstruction6622
  · exact NewCertificates0206.obstruction6623
  · exact NewCertificates0207.obstruction6624
  · exact NewCertificates0207.obstruction6625
  · exact NewCertificates0207.obstruction6626
  · exact NewCertificates0207.obstruction6627
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0207.obstruction6628
  · exact NewCertificates0207.obstruction6629
  · exact NewCertificates0207.obstruction6630
  · exact NewCertificates0207.obstruction6631
  · exact NewCertificates0207.obstruction6632
  · exact NewCertificates0207.obstruction6633
  · exact NewCertificates0207.obstruction6634
  · exact NewCertificates0207.obstruction6635
  · exact NewCertificates0207.obstruction6636
  · exact NewCertificates0207.obstruction6637
  · exact NewCertificates0207.obstruction6638
  · exact NewCertificates0207.obstruction6639
  · exact NewCertificates0207.obstruction6640
  · exact NewCertificates0207.obstruction6641
  · exact NewCertificates0207.obstruction6642
  · exact NewCertificates0207.obstruction6643
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0207.obstruction6644
  · exact NewCertificates0207.obstruction6645
  · exact NewCertificates0207.obstruction6646
  · exact NewCertificates0207.obstruction6647
  · exact NewCertificates0207.obstruction6648
  · exact NewCertificates0207.obstruction6649
  · exact NewCertificates0207.obstruction6650
  · exact NewCertificates0207.obstruction6651
  · exact NewCertificates0207.obstruction6652
  · exact NewCertificates0207.obstruction6653
  · exact NewCertificates0207.obstruction6654
  · exact NewCertificates0207.obstruction6655
  · exact NewCertificates0208.obstruction6656
  · exact NewCertificates0208.obstruction6657
  · exact NewCertificates0208.obstruction6658
  · exact NewCertificates0208.obstruction6659
end Nut8.FiniteSupport143
