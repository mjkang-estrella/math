import SupportData145
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport145
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0209.C6708, NewCertificates0209.C6709, NewCertificates0209.C6710, NewCertificates0209.C6711, NewCertificates0209.C6712, NewCertificates0209.C6713, NewCertificates0209.C6714, NewCertificates0209.C6715, NewCertificates0209.C6716, NewCertificates0209.C6717, NewCertificates0209.C6718, NewCertificates0209.C6719, NewCertificates0210.C6720, NewCertificates0210.C6721, NewCertificates0210.C6722, NewCertificates0210.C6723} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0210.C6724, NewCertificates0210.C6725, NewCertificates0210.C6726, NewCertificates0210.C6727, NewCertificates0210.C6728, NewCertificates0210.C6729, NewCertificates0210.C6730, NewCertificates0210.C6731, NewCertificates0210.C6732, NewCertificates0210.C6733, NewCertificates0210.C6734, NewCertificates0210.C6735, NewCertificates0210.C6736, NewCertificates0210.C6737, NewCertificates0210.C6738, NewCertificates0210.C6739} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0210.C6740, NewCertificates0210.C6741, NewCertificates0210.C6742, NewCertificates0210.C6743, NewCertificates0210.C6744, NewCertificates0210.C6745, NewCertificates0210.C6746, NewCertificates0210.C6747, NewCertificates0210.C6748, NewCertificates0210.C6749, NewCertificates0210.C6750, NewCertificates0210.C6751, NewCertificates0211.C6752, NewCertificates0211.C6753, NewCertificates0211.C6754, NewCertificates0211.C6755} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0209.obstruction6708
  · exact NewCertificates0209.obstruction6709
  · exact NewCertificates0209.obstruction6710
  · exact NewCertificates0209.obstruction6711
  · exact NewCertificates0209.obstruction6712
  · exact NewCertificates0209.obstruction6713
  · exact NewCertificates0209.obstruction6714
  · exact NewCertificates0209.obstruction6715
  · exact NewCertificates0209.obstruction6716
  · exact NewCertificates0209.obstruction6717
  · exact NewCertificates0209.obstruction6718
  · exact NewCertificates0209.obstruction6719
  · exact NewCertificates0210.obstruction6720
  · exact NewCertificates0210.obstruction6721
  · exact NewCertificates0210.obstruction6722
  · exact NewCertificates0210.obstruction6723
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0210.obstruction6724
  · exact NewCertificates0210.obstruction6725
  · exact NewCertificates0210.obstruction6726
  · exact NewCertificates0210.obstruction6727
  · exact NewCertificates0210.obstruction6728
  · exact NewCertificates0210.obstruction6729
  · exact NewCertificates0210.obstruction6730
  · exact NewCertificates0210.obstruction6731
  · exact NewCertificates0210.obstruction6732
  · exact NewCertificates0210.obstruction6733
  · exact NewCertificates0210.obstruction6734
  · exact NewCertificates0210.obstruction6735
  · exact NewCertificates0210.obstruction6736
  · exact NewCertificates0210.obstruction6737
  · exact NewCertificates0210.obstruction6738
  · exact NewCertificates0210.obstruction6739
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0210.obstruction6740
  · exact NewCertificates0210.obstruction6741
  · exact NewCertificates0210.obstruction6742
  · exact NewCertificates0210.obstruction6743
  · exact NewCertificates0210.obstruction6744
  · exact NewCertificates0210.obstruction6745
  · exact NewCertificates0210.obstruction6746
  · exact NewCertificates0210.obstruction6747
  · exact NewCertificates0210.obstruction6748
  · exact NewCertificates0210.obstruction6749
  · exact NewCertificates0210.obstruction6750
  · exact NewCertificates0210.obstruction6751
  · exact NewCertificates0211.obstruction6752
  · exact NewCertificates0211.obstruction6753
  · exact NewCertificates0211.obstruction6754
  · exact NewCertificates0211.obstruction6755
end Nut8.FiniteSupport145
