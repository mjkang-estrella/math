import SupportData013
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport013
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0018.C592, NewCertificates0018.C593, NewCertificates0018.C594, NewCertificates0018.C595, NewCertificates0018.C596, NewCertificates0018.C597, NewCertificates0018.C598, NewCertificates0018.C599, NewCertificates0018.C600, NewCertificates0018.C601, NewCertificates0018.C602, NewCertificates0018.C603, NewCertificates0018.C604, NewCertificates0018.C605, NewCertificates0018.C606, NewCertificates0018.C607, NewCertificates0019.C608, NewCertificates0019.C609, NewCertificates0019.C610, NewCertificates0019.C611, NewCertificates0019.C612, NewCertificates0019.C613, NewCertificates0019.C614, NewCertificates0019.C615, NewCertificates0019.C616, NewCertificates0019.C617, NewCertificates0019.C618, NewCertificates0019.C619, NewCertificates0019.C620, NewCertificates0019.C621, NewCertificates0019.C622, NewCertificates0019.C623} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0019.C624, NewCertificates0019.C625, NewCertificates0019.C626, NewCertificates0019.C627, NewCertificates0019.C628, NewCertificates0019.C629, NewCertificates0019.C630, NewCertificates0019.C631, NewCertificates0019.C632, NewCertificates0019.C633, NewCertificates0019.C634, NewCertificates0019.C635, NewCertificates0019.C636, NewCertificates0019.C637, NewCertificates0019.C638, NewCertificates0019.C639} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0020.C640, NewCertificates0020.C641, NewCertificates0020.C642, NewCertificates0020.C643, NewCertificates0020.C644, NewCertificates0020.C645, NewCertificates0020.C646, NewCertificates0020.C647, NewCertificates0020.C648, NewCertificates0020.C649, NewCertificates0020.C650, NewCertificates0020.C651, NewCertificates0020.C652, NewCertificates0020.C653, NewCertificates0020.C654, NewCertificates0020.C655} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0020.C656, NewCertificates0020.C657, NewCertificates0020.C658, NewCertificates0020.C659, NewCertificates0020.C660, NewCertificates0020.C661, NewCertificates0020.C662, NewCertificates0020.C663} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0018.obstruction592
  · exact NewCertificates0018.obstruction593
  · exact NewCertificates0018.obstruction594
  · exact NewCertificates0018.obstruction595
  · exact NewCertificates0018.obstruction596
  · exact NewCertificates0018.obstruction597
  · exact NewCertificates0018.obstruction598
  · exact NewCertificates0018.obstruction599
  · exact NewCertificates0018.obstruction600
  · exact NewCertificates0018.obstruction601
  · exact NewCertificates0018.obstruction602
  · exact NewCertificates0018.obstruction603
  · exact NewCertificates0018.obstruction604
  · exact NewCertificates0018.obstruction605
  · exact NewCertificates0018.obstruction606
  · exact NewCertificates0018.obstruction607
  · exact NewCertificates0019.obstruction608
  · exact NewCertificates0019.obstruction609
  · exact NewCertificates0019.obstruction610
  · exact NewCertificates0019.obstruction611
  · exact NewCertificates0019.obstruction612
  · exact NewCertificates0019.obstruction613
  · exact NewCertificates0019.obstruction614
  · exact NewCertificates0019.obstruction615
  · exact NewCertificates0019.obstruction616
  · exact NewCertificates0019.obstruction617
  · exact NewCertificates0019.obstruction618
  · exact NewCertificates0019.obstruction619
  · exact NewCertificates0019.obstruction620
  · exact NewCertificates0019.obstruction621
  · exact NewCertificates0019.obstruction622
  · exact NewCertificates0019.obstruction623
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0019.obstruction624
  · exact NewCertificates0019.obstruction625
  · exact NewCertificates0019.obstruction626
  · exact NewCertificates0019.obstruction627
  · exact NewCertificates0019.obstruction628
  · exact NewCertificates0019.obstruction629
  · exact NewCertificates0019.obstruction630
  · exact NewCertificates0019.obstruction631
  · exact NewCertificates0019.obstruction632
  · exact NewCertificates0019.obstruction633
  · exact NewCertificates0019.obstruction634
  · exact NewCertificates0019.obstruction635
  · exact NewCertificates0019.obstruction636
  · exact NewCertificates0019.obstruction637
  · exact NewCertificates0019.obstruction638
  · exact NewCertificates0019.obstruction639
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0020.obstruction640
  · exact NewCertificates0020.obstruction641
  · exact NewCertificates0020.obstruction642
  · exact NewCertificates0020.obstruction643
  · exact NewCertificates0020.obstruction644
  · exact NewCertificates0020.obstruction645
  · exact NewCertificates0020.obstruction646
  · exact NewCertificates0020.obstruction647
  · exact NewCertificates0020.obstruction648
  · exact NewCertificates0020.obstruction649
  · exact NewCertificates0020.obstruction650
  · exact NewCertificates0020.obstruction651
  · exact NewCertificates0020.obstruction652
  · exact NewCertificates0020.obstruction653
  · exact NewCertificates0020.obstruction654
  · exact NewCertificates0020.obstruction655
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0020.obstruction656
  · exact NewCertificates0020.obstruction657
  · exact NewCertificates0020.obstruction658
  · exact NewCertificates0020.obstruction659
  · exact NewCertificates0020.obstruction660
  · exact NewCertificates0020.obstruction661
  · exact NewCertificates0020.obstruction662
  · exact NewCertificates0020.obstruction663
end Nut8.FiniteSupport013
