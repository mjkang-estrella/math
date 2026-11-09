import SupportData147
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport147
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0212.C6792, NewCertificates0212.C6793, NewCertificates0212.C6794, NewCertificates0212.C6795, NewCertificates0212.C6796, NewCertificates0212.C6797, NewCertificates0212.C6798, NewCertificates0212.C6799, NewCertificates0212.C6800, NewCertificates0212.C6801, NewCertificates0212.C6802, NewCertificates0212.C6803, NewCertificates0212.C6804, NewCertificates0212.C6805, NewCertificates0212.C6806, NewCertificates0212.C6807} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0212.C6808, NewCertificates0212.C6809, NewCertificates0212.C6810, NewCertificates0212.C6811, NewCertificates0212.C6812, NewCertificates0212.C6813, NewCertificates0212.C6814, NewCertificates0212.C6815} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0213.C6816, NewCertificates0213.C6817, NewCertificates0213.C6818, NewCertificates0213.C6819, NewCertificates0213.C6820, NewCertificates0213.C6821, NewCertificates0213.C6822, NewCertificates0213.C6823, NewCertificates0213.C6824, NewCertificates0213.C6825, NewCertificates0213.C6826, NewCertificates0213.C6827, NewCertificates0213.C6828, NewCertificates0213.C6829, NewCertificates0213.C6830, NewCertificates0213.C6831} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0213.C6832, NewCertificates0213.C6833, NewCertificates0213.C6834, NewCertificates0213.C6835, NewCertificates0213.C6836, NewCertificates0213.C6837, NewCertificates0213.C6838, NewCertificates0213.C6839} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0212.obstruction6792
  · exact NewCertificates0212.obstruction6793
  · exact NewCertificates0212.obstruction6794
  · exact NewCertificates0212.obstruction6795
  · exact NewCertificates0212.obstruction6796
  · exact NewCertificates0212.obstruction6797
  · exact NewCertificates0212.obstruction6798
  · exact NewCertificates0212.obstruction6799
  · exact NewCertificates0212.obstruction6800
  · exact NewCertificates0212.obstruction6801
  · exact NewCertificates0212.obstruction6802
  · exact NewCertificates0212.obstruction6803
  · exact NewCertificates0212.obstruction6804
  · exact NewCertificates0212.obstruction6805
  · exact NewCertificates0212.obstruction6806
  · exact NewCertificates0212.obstruction6807
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0212.obstruction6808
  · exact NewCertificates0212.obstruction6809
  · exact NewCertificates0212.obstruction6810
  · exact NewCertificates0212.obstruction6811
  · exact NewCertificates0212.obstruction6812
  · exact NewCertificates0212.obstruction6813
  · exact NewCertificates0212.obstruction6814
  · exact NewCertificates0212.obstruction6815
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0213.obstruction6816
  · exact NewCertificates0213.obstruction6817
  · exact NewCertificates0213.obstruction6818
  · exact NewCertificates0213.obstruction6819
  · exact NewCertificates0213.obstruction6820
  · exact NewCertificates0213.obstruction6821
  · exact NewCertificates0213.obstruction6822
  · exact NewCertificates0213.obstruction6823
  · exact NewCertificates0213.obstruction6824
  · exact NewCertificates0213.obstruction6825
  · exact NewCertificates0213.obstruction6826
  · exact NewCertificates0213.obstruction6827
  · exact NewCertificates0213.obstruction6828
  · exact NewCertificates0213.obstruction6829
  · exact NewCertificates0213.obstruction6830
  · exact NewCertificates0213.obstruction6831
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0213.obstruction6832
  · exact NewCertificates0213.obstruction6833
  · exact NewCertificates0213.obstruction6834
  · exact NewCertificates0213.obstruction6835
  · exact NewCertificates0213.obstruction6836
  · exact NewCertificates0213.obstruction6837
  · exact NewCertificates0213.obstruction6838
  · exact NewCertificates0213.obstruction6839
end Nut8.FiniteSupport147
