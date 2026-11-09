import SupportData142
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport142
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0205.C6580, NewCertificates0205.C6581, NewCertificates0205.C6582, NewCertificates0205.C6583, NewCertificates0205.C6584, NewCertificates0205.C6585, NewCertificates0205.C6586, NewCertificates0205.C6587, NewCertificates0205.C6588, NewCertificates0205.C6589, NewCertificates0205.C6590, NewCertificates0205.C6591, NewCertificates0206.C6592, NewCertificates0206.C6593, NewCertificates0206.C6594, NewCertificates0206.C6595, NewCertificates0206.C6596, NewCertificates0206.C6597, NewCertificates0206.C6598, NewCertificates0206.C6599, NewCertificates0206.C6600, NewCertificates0206.C6601, NewCertificates0206.C6602, NewCertificates0206.C6603, NewCertificates0206.C6604, NewCertificates0206.C6605, NewCertificates0206.C6606, NewCertificates0206.C6607, NewCertificates0206.C6608, NewCertificates0206.C6609, NewCertificates0206.C6610, NewCertificates0206.C6611} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0205.obstruction6580
  · exact NewCertificates0205.obstruction6581
  · exact NewCertificates0205.obstruction6582
  · exact NewCertificates0205.obstruction6583
  · exact NewCertificates0205.obstruction6584
  · exact NewCertificates0205.obstruction6585
  · exact NewCertificates0205.obstruction6586
  · exact NewCertificates0205.obstruction6587
  · exact NewCertificates0205.obstruction6588
  · exact NewCertificates0205.obstruction6589
  · exact NewCertificates0205.obstruction6590
  · exact NewCertificates0205.obstruction6591
  · exact NewCertificates0206.obstruction6592
  · exact NewCertificates0206.obstruction6593
  · exact NewCertificates0206.obstruction6594
  · exact NewCertificates0206.obstruction6595
  · exact NewCertificates0206.obstruction6596
  · exact NewCertificates0206.obstruction6597
  · exact NewCertificates0206.obstruction6598
  · exact NewCertificates0206.obstruction6599
  · exact NewCertificates0206.obstruction6600
  · exact NewCertificates0206.obstruction6601
  · exact NewCertificates0206.obstruction6602
  · exact NewCertificates0206.obstruction6603
  · exact NewCertificates0206.obstruction6604
  · exact NewCertificates0206.obstruction6605
  · exact NewCertificates0206.obstruction6606
  · exact NewCertificates0206.obstruction6607
  · exact NewCertificates0206.obstruction6608
  · exact NewCertificates0206.obstruction6609
  · exact NewCertificates0206.obstruction6610
  · exact NewCertificates0206.obstruction6611
end Nut8.FiniteSupport142
