import SupportData119
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport119
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0177.C5676, NewCertificates0177.C5677, NewCertificates0177.C5678, NewCertificates0177.C5679, NewCertificates0177.C5680, NewCertificates0177.C5681, NewCertificates0177.C5682, NewCertificates0177.C5683} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0177.C5684, NewCertificates0177.C5685, NewCertificates0177.C5686, NewCertificates0177.C5687, NewCertificates0177.C5688, NewCertificates0177.C5689, NewCertificates0177.C5690, NewCertificates0177.C5691} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0177.C5692, NewCertificates0177.C5693, NewCertificates0177.C5694, NewCertificates0177.C5695, NewCertificates0178.C5696, NewCertificates0178.C5697, NewCertificates0178.C5698, NewCertificates0178.C5699} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0178.C5700, NewCertificates0178.C5701, NewCertificates0178.C5702, NewCertificates0178.C5703, NewCertificates0178.C5704, NewCertificates0178.C5705, NewCertificates0178.C5706, NewCertificates0178.C5707} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0177.obstruction5676
  · exact NewCertificates0177.obstruction5677
  · exact NewCertificates0177.obstruction5678
  · exact NewCertificates0177.obstruction5679
  · exact NewCertificates0177.obstruction5680
  · exact NewCertificates0177.obstruction5681
  · exact NewCertificates0177.obstruction5682
  · exact NewCertificates0177.obstruction5683
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0177.obstruction5684
  · exact NewCertificates0177.obstruction5685
  · exact NewCertificates0177.obstruction5686
  · exact NewCertificates0177.obstruction5687
  · exact NewCertificates0177.obstruction5688
  · exact NewCertificates0177.obstruction5689
  · exact NewCertificates0177.obstruction5690
  · exact NewCertificates0177.obstruction5691
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0177.obstruction5692
  · exact NewCertificates0177.obstruction5693
  · exact NewCertificates0177.obstruction5694
  · exact NewCertificates0177.obstruction5695
  · exact NewCertificates0178.obstruction5696
  · exact NewCertificates0178.obstruction5697
  · exact NewCertificates0178.obstruction5698
  · exact NewCertificates0178.obstruction5699
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0178.obstruction5700
  · exact NewCertificates0178.obstruction5701
  · exact NewCertificates0178.obstruction5702
  · exact NewCertificates0178.obstruction5703
  · exact NewCertificates0178.obstruction5704
  · exact NewCertificates0178.obstruction5705
  · exact NewCertificates0178.obstruction5706
  · exact NewCertificates0178.obstruction5707
end Nut8.FiniteSupport119
