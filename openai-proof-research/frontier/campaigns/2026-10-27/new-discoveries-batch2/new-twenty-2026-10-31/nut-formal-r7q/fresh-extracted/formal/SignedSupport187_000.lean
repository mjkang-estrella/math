import SupportData187
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport187
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0275.C8812, NewCertificates0275.C8813, NewCertificates0275.C8814, NewCertificates0275.C8815, NewCertificates0275.C8816, NewCertificates0275.C8817, NewCertificates0275.C8818, NewCertificates0275.C8819, NewCertificates0275.C8820, NewCertificates0275.C8821, NewCertificates0275.C8822, NewCertificates0275.C8823, NewCertificates0275.C8824, NewCertificates0275.C8825, NewCertificates0275.C8826, NewCertificates0275.C8827, NewCertificates0275.C8828, NewCertificates0275.C8829, NewCertificates0275.C8830, NewCertificates0275.C8831, NewCertificates0276.C8832, NewCertificates0276.C8833, NewCertificates0276.C8834, NewCertificates0276.C8835, NewCertificates0276.C8836, NewCertificates0276.C8837, NewCertificates0276.C8838, NewCertificates0276.C8839, NewCertificates0276.C8840, NewCertificates0276.C8841, NewCertificates0276.C8842, NewCertificates0276.C8843} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0276.C8844, NewCertificates0276.C8845, NewCertificates0276.C8846, NewCertificates0276.C8847, NewCertificates0276.C8848, NewCertificates0276.C8849, NewCertificates0276.C8850, NewCertificates0276.C8851, NewCertificates0276.C8852, NewCertificates0276.C8853, NewCertificates0276.C8854, NewCertificates0276.C8855, NewCertificates0276.C8856, NewCertificates0276.C8857, NewCertificates0276.C8858, NewCertificates0276.C8859} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0276.C8860, NewCertificates0276.C8861, NewCertificates0276.C8862, NewCertificates0276.C8863, NewCertificates0277.C8864, NewCertificates0277.C8865, NewCertificates0277.C8866, NewCertificates0277.C8867, NewCertificates0277.C8868, NewCertificates0277.C8869, NewCertificates0277.C8870, NewCertificates0277.C8871, NewCertificates0277.C8872, NewCertificates0277.C8873, NewCertificates0277.C8874, NewCertificates0277.C8875} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0275.obstruction8812
  · exact NewCertificates0275.obstruction8813
  · exact NewCertificates0275.obstruction8814
  · exact NewCertificates0275.obstruction8815
  · exact NewCertificates0275.obstruction8816
  · exact NewCertificates0275.obstruction8817
  · exact NewCertificates0275.obstruction8818
  · exact NewCertificates0275.obstruction8819
  · exact NewCertificates0275.obstruction8820
  · exact NewCertificates0275.obstruction8821
  · exact NewCertificates0275.obstruction8822
  · exact NewCertificates0275.obstruction8823
  · exact NewCertificates0275.obstruction8824
  · exact NewCertificates0275.obstruction8825
  · exact NewCertificates0275.obstruction8826
  · exact NewCertificates0275.obstruction8827
  · exact NewCertificates0275.obstruction8828
  · exact NewCertificates0275.obstruction8829
  · exact NewCertificates0275.obstruction8830
  · exact NewCertificates0275.obstruction8831
  · exact NewCertificates0276.obstruction8832
  · exact NewCertificates0276.obstruction8833
  · exact NewCertificates0276.obstruction8834
  · exact NewCertificates0276.obstruction8835
  · exact NewCertificates0276.obstruction8836
  · exact NewCertificates0276.obstruction8837
  · exact NewCertificates0276.obstruction8838
  · exact NewCertificates0276.obstruction8839
  · exact NewCertificates0276.obstruction8840
  · exact NewCertificates0276.obstruction8841
  · exact NewCertificates0276.obstruction8842
  · exact NewCertificates0276.obstruction8843
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0276.obstruction8844
  · exact NewCertificates0276.obstruction8845
  · exact NewCertificates0276.obstruction8846
  · exact NewCertificates0276.obstruction8847
  · exact NewCertificates0276.obstruction8848
  · exact NewCertificates0276.obstruction8849
  · exact NewCertificates0276.obstruction8850
  · exact NewCertificates0276.obstruction8851
  · exact NewCertificates0276.obstruction8852
  · exact NewCertificates0276.obstruction8853
  · exact NewCertificates0276.obstruction8854
  · exact NewCertificates0276.obstruction8855
  · exact NewCertificates0276.obstruction8856
  · exact NewCertificates0276.obstruction8857
  · exact NewCertificates0276.obstruction8858
  · exact NewCertificates0276.obstruction8859
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0276.obstruction8860
  · exact NewCertificates0276.obstruction8861
  · exact NewCertificates0276.obstruction8862
  · exact NewCertificates0276.obstruction8863
  · exact NewCertificates0277.obstruction8864
  · exact NewCertificates0277.obstruction8865
  · exact NewCertificates0277.obstruction8866
  · exact NewCertificates0277.obstruction8867
  · exact NewCertificates0277.obstruction8868
  · exact NewCertificates0277.obstruction8869
  · exact NewCertificates0277.obstruction8870
  · exact NewCertificates0277.obstruction8871
  · exact NewCertificates0277.obstruction8872
  · exact NewCertificates0277.obstruction8873
  · exact NewCertificates0277.obstruction8874
  · exact NewCertificates0277.obstruction8875
end Nut8.FiniteSupport187
