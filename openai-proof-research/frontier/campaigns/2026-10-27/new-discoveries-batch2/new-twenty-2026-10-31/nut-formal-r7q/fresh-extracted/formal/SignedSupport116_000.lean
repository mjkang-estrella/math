import SupportData116
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport116
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0174.C5580, NewCertificates0174.C5581, NewCertificates0174.C5582, NewCertificates0174.C5583, NewCertificates0174.C5584, NewCertificates0174.C5585, NewCertificates0174.C5586, NewCertificates0174.C5587, NewCertificates0174.C5588, NewCertificates0174.C5589, NewCertificates0174.C5590, NewCertificates0174.C5591, NewCertificates0174.C5592, NewCertificates0174.C5593, NewCertificates0174.C5594, NewCertificates0174.C5595, NewCertificates0174.C5596, NewCertificates0174.C5597, NewCertificates0174.C5598, NewCertificates0174.C5599, NewCertificates0175.C5600, NewCertificates0175.C5601, NewCertificates0175.C5602, NewCertificates0175.C5603, NewCertificates0175.C5604, NewCertificates0175.C5605, NewCertificates0175.C5606, NewCertificates0175.C5607, NewCertificates0175.C5608, NewCertificates0175.C5609, NewCertificates0175.C5610, NewCertificates0175.C5611} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0174.obstruction5580
  · exact NewCertificates0174.obstruction5581
  · exact NewCertificates0174.obstruction5582
  · exact NewCertificates0174.obstruction5583
  · exact NewCertificates0174.obstruction5584
  · exact NewCertificates0174.obstruction5585
  · exact NewCertificates0174.obstruction5586
  · exact NewCertificates0174.obstruction5587
  · exact NewCertificates0174.obstruction5588
  · exact NewCertificates0174.obstruction5589
  · exact NewCertificates0174.obstruction5590
  · exact NewCertificates0174.obstruction5591
  · exact NewCertificates0174.obstruction5592
  · exact NewCertificates0174.obstruction5593
  · exact NewCertificates0174.obstruction5594
  · exact NewCertificates0174.obstruction5595
  · exact NewCertificates0174.obstruction5596
  · exact NewCertificates0174.obstruction5597
  · exact NewCertificates0174.obstruction5598
  · exact NewCertificates0174.obstruction5599
  · exact NewCertificates0175.obstruction5600
  · exact NewCertificates0175.obstruction5601
  · exact NewCertificates0175.obstruction5602
  · exact NewCertificates0175.obstruction5603
  · exact NewCertificates0175.obstruction5604
  · exact NewCertificates0175.obstruction5605
  · exact NewCertificates0175.obstruction5606
  · exact NewCertificates0175.obstruction5607
  · exact NewCertificates0175.obstruction5608
  · exact NewCertificates0175.obstruction5609
  · exact NewCertificates0175.obstruction5610
  · exact NewCertificates0175.obstruction5611
end Nut8.FiniteSupport116
