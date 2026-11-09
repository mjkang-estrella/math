import SupportData014
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport014
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0020.C664, NewCertificates0020.C665, NewCertificates0020.C666, NewCertificates0020.C667, NewCertificates0020.C668, NewCertificates0020.C669, NewCertificates0020.C670, NewCertificates0020.C671, NewCertificates0021.C672, NewCertificates0021.C673, NewCertificates0021.C674, NewCertificates0021.C675, NewCertificates0021.C676, NewCertificates0021.C677, NewCertificates0021.C678, NewCertificates0021.C679} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0021.C680, NewCertificates0021.C681, NewCertificates0021.C682, NewCertificates0021.C683, NewCertificates0021.C684, NewCertificates0021.C685, NewCertificates0021.C686, NewCertificates0021.C687, NewCertificates0021.C688, NewCertificates0021.C689, NewCertificates0021.C690, NewCertificates0021.C691, NewCertificates0021.C692, NewCertificates0021.C693, NewCertificates0021.C694, NewCertificates0021.C695} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0021.C696, NewCertificates0021.C697, NewCertificates0021.C698, NewCertificates0021.C699, NewCertificates0021.C700, NewCertificates0021.C701, NewCertificates0021.C702, NewCertificates0021.C703, NewCertificates0022.C704, NewCertificates0022.C705, NewCertificates0022.C706, NewCertificates0022.C707, NewCertificates0022.C708, NewCertificates0022.C709, NewCertificates0022.C710, NewCertificates0022.C711} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0022.C712, NewCertificates0022.C713, NewCertificates0022.C714, NewCertificates0022.C715, NewCertificates0022.C716, NewCertificates0022.C717, NewCertificates0022.C718, NewCertificates0022.C719} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0020.obstruction664
  · exact NewCertificates0020.obstruction665
  · exact NewCertificates0020.obstruction666
  · exact NewCertificates0020.obstruction667
  · exact NewCertificates0020.obstruction668
  · exact NewCertificates0020.obstruction669
  · exact NewCertificates0020.obstruction670
  · exact NewCertificates0020.obstruction671
  · exact NewCertificates0021.obstruction672
  · exact NewCertificates0021.obstruction673
  · exact NewCertificates0021.obstruction674
  · exact NewCertificates0021.obstruction675
  · exact NewCertificates0021.obstruction676
  · exact NewCertificates0021.obstruction677
  · exact NewCertificates0021.obstruction678
  · exact NewCertificates0021.obstruction679
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0021.obstruction680
  · exact NewCertificates0021.obstruction681
  · exact NewCertificates0021.obstruction682
  · exact NewCertificates0021.obstruction683
  · exact NewCertificates0021.obstruction684
  · exact NewCertificates0021.obstruction685
  · exact NewCertificates0021.obstruction686
  · exact NewCertificates0021.obstruction687
  · exact NewCertificates0021.obstruction688
  · exact NewCertificates0021.obstruction689
  · exact NewCertificates0021.obstruction690
  · exact NewCertificates0021.obstruction691
  · exact NewCertificates0021.obstruction692
  · exact NewCertificates0021.obstruction693
  · exact NewCertificates0021.obstruction694
  · exact NewCertificates0021.obstruction695
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0021.obstruction696
  · exact NewCertificates0021.obstruction697
  · exact NewCertificates0021.obstruction698
  · exact NewCertificates0021.obstruction699
  · exact NewCertificates0021.obstruction700
  · exact NewCertificates0021.obstruction701
  · exact NewCertificates0021.obstruction702
  · exact NewCertificates0021.obstruction703
  · exact NewCertificates0022.obstruction704
  · exact NewCertificates0022.obstruction705
  · exact NewCertificates0022.obstruction706
  · exact NewCertificates0022.obstruction707
  · exact NewCertificates0022.obstruction708
  · exact NewCertificates0022.obstruction709
  · exact NewCertificates0022.obstruction710
  · exact NewCertificates0022.obstruction711
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0022.obstruction712
  · exact NewCertificates0022.obstruction713
  · exact NewCertificates0022.obstruction714
  · exact NewCertificates0022.obstruction715
  · exact NewCertificates0022.obstruction716
  · exact NewCertificates0022.obstruction717
  · exact NewCertificates0022.obstruction718
  · exact NewCertificates0022.obstruction719
end Nut8.FiniteSupport014
