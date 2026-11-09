import SupportData144
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport144
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0208.C6660, NewCertificates0208.C6661, NewCertificates0208.C6662, NewCertificates0208.C6663, NewCertificates0208.C6664, NewCertificates0208.C6665, NewCertificates0208.C6666, NewCertificates0208.C6667, NewCertificates0208.C6668, NewCertificates0208.C6669, NewCertificates0208.C6670, NewCertificates0208.C6671, NewCertificates0208.C6672, NewCertificates0208.C6673, NewCertificates0208.C6674, NewCertificates0208.C6675} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0208.C6676, NewCertificates0208.C6677, NewCertificates0208.C6678, NewCertificates0208.C6679, NewCertificates0208.C6680, NewCertificates0208.C6681, NewCertificates0208.C6682, NewCertificates0208.C6683, NewCertificates0208.C6684, NewCertificates0208.C6685, NewCertificates0208.C6686, NewCertificates0208.C6687, NewCertificates0209.C6688, NewCertificates0209.C6689, NewCertificates0209.C6690, NewCertificates0209.C6691} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0209.C6692, NewCertificates0209.C6693, NewCertificates0209.C6694, NewCertificates0209.C6695, NewCertificates0209.C6696, NewCertificates0209.C6697, NewCertificates0209.C6698, NewCertificates0209.C6699, NewCertificates0209.C6700, NewCertificates0209.C6701, NewCertificates0209.C6702, NewCertificates0209.C6703, NewCertificates0209.C6704, NewCertificates0209.C6705, NewCertificates0209.C6706, NewCertificates0209.C6707} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0208.obstruction6660
  · exact NewCertificates0208.obstruction6661
  · exact NewCertificates0208.obstruction6662
  · exact NewCertificates0208.obstruction6663
  · exact NewCertificates0208.obstruction6664
  · exact NewCertificates0208.obstruction6665
  · exact NewCertificates0208.obstruction6666
  · exact NewCertificates0208.obstruction6667
  · exact NewCertificates0208.obstruction6668
  · exact NewCertificates0208.obstruction6669
  · exact NewCertificates0208.obstruction6670
  · exact NewCertificates0208.obstruction6671
  · exact NewCertificates0208.obstruction6672
  · exact NewCertificates0208.obstruction6673
  · exact NewCertificates0208.obstruction6674
  · exact NewCertificates0208.obstruction6675
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0208.obstruction6676
  · exact NewCertificates0208.obstruction6677
  · exact NewCertificates0208.obstruction6678
  · exact NewCertificates0208.obstruction6679
  · exact NewCertificates0208.obstruction6680
  · exact NewCertificates0208.obstruction6681
  · exact NewCertificates0208.obstruction6682
  · exact NewCertificates0208.obstruction6683
  · exact NewCertificates0208.obstruction6684
  · exact NewCertificates0208.obstruction6685
  · exact NewCertificates0208.obstruction6686
  · exact NewCertificates0208.obstruction6687
  · exact NewCertificates0209.obstruction6688
  · exact NewCertificates0209.obstruction6689
  · exact NewCertificates0209.obstruction6690
  · exact NewCertificates0209.obstruction6691
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0209.obstruction6692
  · exact NewCertificates0209.obstruction6693
  · exact NewCertificates0209.obstruction6694
  · exact NewCertificates0209.obstruction6695
  · exact NewCertificates0209.obstruction6696
  · exact NewCertificates0209.obstruction6697
  · exact NewCertificates0209.obstruction6698
  · exact NewCertificates0209.obstruction6699
  · exact NewCertificates0209.obstruction6700
  · exact NewCertificates0209.obstruction6701
  · exact NewCertificates0209.obstruction6702
  · exact NewCertificates0209.obstruction6703
  · exact NewCertificates0209.obstruction6704
  · exact NewCertificates0209.obstruction6705
  · exact NewCertificates0209.obstruction6706
  · exact NewCertificates0209.obstruction6707
end Nut8.FiniteSupport144
