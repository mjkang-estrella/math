import SupportData016
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport016
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0023.C752, NewCertificates0023.C753, NewCertificates0023.C754, NewCertificates0023.C755, NewCertificates0023.C756, NewCertificates0023.C757, NewCertificates0023.C758, NewCertificates0023.C759, NewCertificates0023.C760, NewCertificates0023.C761, NewCertificates0023.C762, NewCertificates0023.C763, NewCertificates0023.C764, NewCertificates0023.C765, NewCertificates0023.C766, NewCertificates0023.C767} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0024.C768, NewCertificates0024.C769, NewCertificates0024.C770, NewCertificates0024.C771, NewCertificates0024.C772, NewCertificates0024.C773, NewCertificates0024.C774, NewCertificates0024.C775, NewCertificates0024.C776, NewCertificates0024.C777, NewCertificates0024.C778, NewCertificates0024.C779, NewCertificates0024.C780, NewCertificates0024.C781, NewCertificates0024.C782, NewCertificates0024.C783} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0024.C784, NewCertificates0024.C785, NewCertificates0024.C786, NewCertificates0024.C787, NewCertificates0024.C788, NewCertificates0024.C789, NewCertificates0024.C790, NewCertificates0024.C791, NewCertificates0024.C792, NewCertificates0024.C793, NewCertificates0024.C794, NewCertificates0024.C795, NewCertificates0024.C796, NewCertificates0024.C797, NewCertificates0024.C798, NewCertificates0024.C799} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0025.C800, NewCertificates0025.C801, NewCertificates0025.C802, NewCertificates0025.C803, NewCertificates0025.C804, NewCertificates0025.C805, NewCertificates0025.C806, NewCertificates0025.C807, NewCertificates0025.C808, NewCertificates0025.C809, NewCertificates0025.C810, NewCertificates0025.C811, NewCertificates0025.C812, NewCertificates0025.C813, NewCertificates0025.C814, NewCertificates0025.C815} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0023.obstruction752
  · exact NewCertificates0023.obstruction753
  · exact NewCertificates0023.obstruction754
  · exact NewCertificates0023.obstruction755
  · exact NewCertificates0023.obstruction756
  · exact NewCertificates0023.obstruction757
  · exact NewCertificates0023.obstruction758
  · exact NewCertificates0023.obstruction759
  · exact NewCertificates0023.obstruction760
  · exact NewCertificates0023.obstruction761
  · exact NewCertificates0023.obstruction762
  · exact NewCertificates0023.obstruction763
  · exact NewCertificates0023.obstruction764
  · exact NewCertificates0023.obstruction765
  · exact NewCertificates0023.obstruction766
  · exact NewCertificates0023.obstruction767
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0024.obstruction768
  · exact NewCertificates0024.obstruction769
  · exact NewCertificates0024.obstruction770
  · exact NewCertificates0024.obstruction771
  · exact NewCertificates0024.obstruction772
  · exact NewCertificates0024.obstruction773
  · exact NewCertificates0024.obstruction774
  · exact NewCertificates0024.obstruction775
  · exact NewCertificates0024.obstruction776
  · exact NewCertificates0024.obstruction777
  · exact NewCertificates0024.obstruction778
  · exact NewCertificates0024.obstruction779
  · exact NewCertificates0024.obstruction780
  · exact NewCertificates0024.obstruction781
  · exact NewCertificates0024.obstruction782
  · exact NewCertificates0024.obstruction783
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0024.obstruction784
  · exact NewCertificates0024.obstruction785
  · exact NewCertificates0024.obstruction786
  · exact NewCertificates0024.obstruction787
  · exact NewCertificates0024.obstruction788
  · exact NewCertificates0024.obstruction789
  · exact NewCertificates0024.obstruction790
  · exact NewCertificates0024.obstruction791
  · exact NewCertificates0024.obstruction792
  · exact NewCertificates0024.obstruction793
  · exact NewCertificates0024.obstruction794
  · exact NewCertificates0024.obstruction795
  · exact NewCertificates0024.obstruction796
  · exact NewCertificates0024.obstruction797
  · exact NewCertificates0024.obstruction798
  · exact NewCertificates0024.obstruction799
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0025.obstruction800
  · exact NewCertificates0025.obstruction801
  · exact NewCertificates0025.obstruction802
  · exact NewCertificates0025.obstruction803
  · exact NewCertificates0025.obstruction804
  · exact NewCertificates0025.obstruction805
  · exact NewCertificates0025.obstruction806
  · exact NewCertificates0025.obstruction807
  · exact NewCertificates0025.obstruction808
  · exact NewCertificates0025.obstruction809
  · exact NewCertificates0025.obstruction810
  · exact NewCertificates0025.obstruction811
  · exact NewCertificates0025.obstruction812
  · exact NewCertificates0025.obstruction813
  · exact NewCertificates0025.obstruction814
  · exact NewCertificates0025.obstruction815
end Nut8.FiniteSupport016
