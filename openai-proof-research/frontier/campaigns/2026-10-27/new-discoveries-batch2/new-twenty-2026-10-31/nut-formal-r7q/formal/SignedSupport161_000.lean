import SupportData161
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport161
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0236.C7572, NewCertificates0236.C7573, NewCertificates0236.C7574, NewCertificates0236.C7575, NewCertificates0236.C7576, NewCertificates0236.C7577, NewCertificates0236.C7578, NewCertificates0236.C7579, NewCertificates0236.C7580, NewCertificates0236.C7581, NewCertificates0236.C7582, NewCertificates0236.C7583, NewCertificates0237.C7584, NewCertificates0237.C7585, NewCertificates0237.C7586, NewCertificates0237.C7587} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0237.C7588, NewCertificates0237.C7589, NewCertificates0237.C7590, NewCertificates0237.C7591, NewCertificates0237.C7592, NewCertificates0237.C7593, NewCertificates0237.C7594, NewCertificates0237.C7595, NewCertificates0237.C7596, NewCertificates0237.C7597, NewCertificates0237.C7598, NewCertificates0237.C7599, NewCertificates0237.C7600, NewCertificates0237.C7601, NewCertificates0237.C7602, NewCertificates0237.C7603} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0237.C7604, NewCertificates0237.C7605, NewCertificates0237.C7606, NewCertificates0237.C7607, NewCertificates0237.C7608, NewCertificates0237.C7609, NewCertificates0237.C7610, NewCertificates0237.C7611, NewCertificates0237.C7612, NewCertificates0237.C7613, NewCertificates0237.C7614, NewCertificates0237.C7615, NewCertificates0238.C7616, NewCertificates0238.C7617, NewCertificates0238.C7618, NewCertificates0238.C7619} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0236.obstruction7572
  · exact NewCertificates0236.obstruction7573
  · exact NewCertificates0236.obstruction7574
  · exact NewCertificates0236.obstruction7575
  · exact NewCertificates0236.obstruction7576
  · exact NewCertificates0236.obstruction7577
  · exact NewCertificates0236.obstruction7578
  · exact NewCertificates0236.obstruction7579
  · exact NewCertificates0236.obstruction7580
  · exact NewCertificates0236.obstruction7581
  · exact NewCertificates0236.obstruction7582
  · exact NewCertificates0236.obstruction7583
  · exact NewCertificates0237.obstruction7584
  · exact NewCertificates0237.obstruction7585
  · exact NewCertificates0237.obstruction7586
  · exact NewCertificates0237.obstruction7587
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0237.obstruction7588
  · exact NewCertificates0237.obstruction7589
  · exact NewCertificates0237.obstruction7590
  · exact NewCertificates0237.obstruction7591
  · exact NewCertificates0237.obstruction7592
  · exact NewCertificates0237.obstruction7593
  · exact NewCertificates0237.obstruction7594
  · exact NewCertificates0237.obstruction7595
  · exact NewCertificates0237.obstruction7596
  · exact NewCertificates0237.obstruction7597
  · exact NewCertificates0237.obstruction7598
  · exact NewCertificates0237.obstruction7599
  · exact NewCertificates0237.obstruction7600
  · exact NewCertificates0237.obstruction7601
  · exact NewCertificates0237.obstruction7602
  · exact NewCertificates0237.obstruction7603
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0237.obstruction7604
  · exact NewCertificates0237.obstruction7605
  · exact NewCertificates0237.obstruction7606
  · exact NewCertificates0237.obstruction7607
  · exact NewCertificates0237.obstruction7608
  · exact NewCertificates0237.obstruction7609
  · exact NewCertificates0237.obstruction7610
  · exact NewCertificates0237.obstruction7611
  · exact NewCertificates0237.obstruction7612
  · exact NewCertificates0237.obstruction7613
  · exact NewCertificates0237.obstruction7614
  · exact NewCertificates0237.obstruction7615
  · exact NewCertificates0238.obstruction7616
  · exact NewCertificates0238.obstruction7617
  · exact NewCertificates0238.obstruction7618
  · exact NewCertificates0238.obstruction7619
end Nut8.FiniteSupport161
