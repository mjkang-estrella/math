import SupportData185
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport185
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0272.C8716, NewCertificates0272.C8717, NewCertificates0272.C8718, NewCertificates0272.C8719, NewCertificates0272.C8720, NewCertificates0272.C8721, NewCertificates0272.C8722, NewCertificates0272.C8723, NewCertificates0272.C8724, NewCertificates0272.C8725, NewCertificates0272.C8726, NewCertificates0272.C8727, NewCertificates0272.C8728, NewCertificates0272.C8729, NewCertificates0272.C8730, NewCertificates0272.C8731, NewCertificates0272.C8732, NewCertificates0272.C8733, NewCertificates0272.C8734, NewCertificates0272.C8735, NewCertificates0273.C8736, NewCertificates0273.C8737, NewCertificates0273.C8738, NewCertificates0273.C8739, NewCertificates0273.C8740, NewCertificates0273.C8741, NewCertificates0273.C8742, NewCertificates0273.C8743, NewCertificates0273.C8744, NewCertificates0273.C8745, NewCertificates0273.C8746, NewCertificates0273.C8747} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0273.C8748, NewCertificates0273.C8749, NewCertificates0273.C8750, NewCertificates0273.C8751, NewCertificates0273.C8752, NewCertificates0273.C8753, NewCertificates0273.C8754, NewCertificates0273.C8755, NewCertificates0273.C8756, NewCertificates0273.C8757, NewCertificates0273.C8758, NewCertificates0273.C8759, NewCertificates0273.C8760, NewCertificates0273.C8761, NewCertificates0273.C8762, NewCertificates0273.C8763} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0272.obstruction8716
  · exact NewCertificates0272.obstruction8717
  · exact NewCertificates0272.obstruction8718
  · exact NewCertificates0272.obstruction8719
  · exact NewCertificates0272.obstruction8720
  · exact NewCertificates0272.obstruction8721
  · exact NewCertificates0272.obstruction8722
  · exact NewCertificates0272.obstruction8723
  · exact NewCertificates0272.obstruction8724
  · exact NewCertificates0272.obstruction8725
  · exact NewCertificates0272.obstruction8726
  · exact NewCertificates0272.obstruction8727
  · exact NewCertificates0272.obstruction8728
  · exact NewCertificates0272.obstruction8729
  · exact NewCertificates0272.obstruction8730
  · exact NewCertificates0272.obstruction8731
  · exact NewCertificates0272.obstruction8732
  · exact NewCertificates0272.obstruction8733
  · exact NewCertificates0272.obstruction8734
  · exact NewCertificates0272.obstruction8735
  · exact NewCertificates0273.obstruction8736
  · exact NewCertificates0273.obstruction8737
  · exact NewCertificates0273.obstruction8738
  · exact NewCertificates0273.obstruction8739
  · exact NewCertificates0273.obstruction8740
  · exact NewCertificates0273.obstruction8741
  · exact NewCertificates0273.obstruction8742
  · exact NewCertificates0273.obstruction8743
  · exact NewCertificates0273.obstruction8744
  · exact NewCertificates0273.obstruction8745
  · exact NewCertificates0273.obstruction8746
  · exact NewCertificates0273.obstruction8747
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0273.obstruction8748
  · exact NewCertificates0273.obstruction8749
  · exact NewCertificates0273.obstruction8750
  · exact NewCertificates0273.obstruction8751
  · exact NewCertificates0273.obstruction8752
  · exact NewCertificates0273.obstruction8753
  · exact NewCertificates0273.obstruction8754
  · exact NewCertificates0273.obstruction8755
  · exact NewCertificates0273.obstruction8756
  · exact NewCertificates0273.obstruction8757
  · exact NewCertificates0273.obstruction8758
  · exact NewCertificates0273.obstruction8759
  · exact NewCertificates0273.obstruction8760
  · exact NewCertificates0273.obstruction8761
  · exact NewCertificates0273.obstruction8762
  · exact NewCertificates0273.obstruction8763
end Nut8.FiniteSupport185
