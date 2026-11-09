import SupportData146
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport146
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0211.C6756, NewCertificates0211.C6757, NewCertificates0211.C6758, NewCertificates0211.C6759, NewCertificates0211.C6760, NewCertificates0211.C6761, NewCertificates0211.C6762, NewCertificates0211.C6763, NewCertificates0211.C6764, NewCertificates0211.C6765, NewCertificates0211.C6766, NewCertificates0211.C6767, NewCertificates0211.C6768, NewCertificates0211.C6769, NewCertificates0211.C6770, NewCertificates0211.C6771} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0211.C6772, NewCertificates0211.C6773, NewCertificates0211.C6774, NewCertificates0211.C6775, NewCertificates0211.C6776, NewCertificates0211.C6777, NewCertificates0211.C6778, NewCertificates0211.C6779} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0211.C6780, NewCertificates0211.C6781, NewCertificates0211.C6782, NewCertificates0211.C6783, NewCertificates0212.C6784, NewCertificates0212.C6785, NewCertificates0212.C6786, NewCertificates0212.C6787} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0212.C6788, NewCertificates0212.C6789, NewCertificates0212.C6790, NewCertificates0212.C6791} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0211.obstruction6756
  · exact NewCertificates0211.obstruction6757
  · exact NewCertificates0211.obstruction6758
  · exact NewCertificates0211.obstruction6759
  · exact NewCertificates0211.obstruction6760
  · exact NewCertificates0211.obstruction6761
  · exact NewCertificates0211.obstruction6762
  · exact NewCertificates0211.obstruction6763
  · exact NewCertificates0211.obstruction6764
  · exact NewCertificates0211.obstruction6765
  · exact NewCertificates0211.obstruction6766
  · exact NewCertificates0211.obstruction6767
  · exact NewCertificates0211.obstruction6768
  · exact NewCertificates0211.obstruction6769
  · exact NewCertificates0211.obstruction6770
  · exact NewCertificates0211.obstruction6771
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0211.obstruction6772
  · exact NewCertificates0211.obstruction6773
  · exact NewCertificates0211.obstruction6774
  · exact NewCertificates0211.obstruction6775
  · exact NewCertificates0211.obstruction6776
  · exact NewCertificates0211.obstruction6777
  · exact NewCertificates0211.obstruction6778
  · exact NewCertificates0211.obstruction6779
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0211.obstruction6780
  · exact NewCertificates0211.obstruction6781
  · exact NewCertificates0211.obstruction6782
  · exact NewCertificates0211.obstruction6783
  · exact NewCertificates0212.obstruction6784
  · exact NewCertificates0212.obstruction6785
  · exact NewCertificates0212.obstruction6786
  · exact NewCertificates0212.obstruction6787
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0212.obstruction6788
  · exact NewCertificates0212.obstruction6789
  · exact NewCertificates0212.obstruction6790
  · exact NewCertificates0212.obstruction6791
end Nut8.FiniteSupport146
