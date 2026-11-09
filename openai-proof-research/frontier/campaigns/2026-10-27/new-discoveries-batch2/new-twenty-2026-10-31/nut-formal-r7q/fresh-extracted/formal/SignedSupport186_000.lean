import SupportData186
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport186
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0273.C8764, NewCertificates0273.C8765, NewCertificates0273.C8766, NewCertificates0273.C8767, NewCertificates0274.C8768, NewCertificates0274.C8769, NewCertificates0274.C8770, NewCertificates0274.C8771, NewCertificates0274.C8772, NewCertificates0274.C8773, NewCertificates0274.C8774, NewCertificates0274.C8775, NewCertificates0274.C8776, NewCertificates0274.C8777, NewCertificates0274.C8778, NewCertificates0274.C8779, NewCertificates0274.C8780, NewCertificates0274.C8781, NewCertificates0274.C8782, NewCertificates0274.C8783, NewCertificates0274.C8784, NewCertificates0274.C8785, NewCertificates0274.C8786, NewCertificates0274.C8787, NewCertificates0274.C8788, NewCertificates0274.C8789, NewCertificates0274.C8790, NewCertificates0274.C8791, NewCertificates0274.C8792, NewCertificates0274.C8793, NewCertificates0274.C8794, NewCertificates0274.C8795} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0274.C8796, NewCertificates0274.C8797, NewCertificates0274.C8798, NewCertificates0274.C8799, NewCertificates0275.C8800, NewCertificates0275.C8801, NewCertificates0275.C8802, NewCertificates0275.C8803, NewCertificates0275.C8804, NewCertificates0275.C8805, NewCertificates0275.C8806, NewCertificates0275.C8807, NewCertificates0275.C8808, NewCertificates0275.C8809, NewCertificates0275.C8810, NewCertificates0275.C8811} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0273.obstruction8764
  · exact NewCertificates0273.obstruction8765
  · exact NewCertificates0273.obstruction8766
  · exact NewCertificates0273.obstruction8767
  · exact NewCertificates0274.obstruction8768
  · exact NewCertificates0274.obstruction8769
  · exact NewCertificates0274.obstruction8770
  · exact NewCertificates0274.obstruction8771
  · exact NewCertificates0274.obstruction8772
  · exact NewCertificates0274.obstruction8773
  · exact NewCertificates0274.obstruction8774
  · exact NewCertificates0274.obstruction8775
  · exact NewCertificates0274.obstruction8776
  · exact NewCertificates0274.obstruction8777
  · exact NewCertificates0274.obstruction8778
  · exact NewCertificates0274.obstruction8779
  · exact NewCertificates0274.obstruction8780
  · exact NewCertificates0274.obstruction8781
  · exact NewCertificates0274.obstruction8782
  · exact NewCertificates0274.obstruction8783
  · exact NewCertificates0274.obstruction8784
  · exact NewCertificates0274.obstruction8785
  · exact NewCertificates0274.obstruction8786
  · exact NewCertificates0274.obstruction8787
  · exact NewCertificates0274.obstruction8788
  · exact NewCertificates0274.obstruction8789
  · exact NewCertificates0274.obstruction8790
  · exact NewCertificates0274.obstruction8791
  · exact NewCertificates0274.obstruction8792
  · exact NewCertificates0274.obstruction8793
  · exact NewCertificates0274.obstruction8794
  · exact NewCertificates0274.obstruction8795
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0274.obstruction8796
  · exact NewCertificates0274.obstruction8797
  · exact NewCertificates0274.obstruction8798
  · exact NewCertificates0274.obstruction8799
  · exact NewCertificates0275.obstruction8800
  · exact NewCertificates0275.obstruction8801
  · exact NewCertificates0275.obstruction8802
  · exact NewCertificates0275.obstruction8803
  · exact NewCertificates0275.obstruction8804
  · exact NewCertificates0275.obstruction8805
  · exact NewCertificates0275.obstruction8806
  · exact NewCertificates0275.obstruction8807
  · exact NewCertificates0275.obstruction8808
  · exact NewCertificates0275.obstruction8809
  · exact NewCertificates0275.obstruction8810
  · exact NewCertificates0275.obstruction8811
end Nut8.FiniteSupport186
