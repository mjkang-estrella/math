import SupportData120
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport120
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0178.C5724, NewCertificates0178.C5725, NewCertificates0178.C5726, NewCertificates0178.C5727, NewCertificates0179.C5728, NewCertificates0179.C5729, NewCertificates0179.C5730, NewCertificates0179.C5731} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0179.C5732, NewCertificates0179.C5733, NewCertificates0179.C5734, NewCertificates0179.C5735, NewCertificates0179.C5736, NewCertificates0179.C5737, NewCertificates0179.C5738, NewCertificates0179.C5739} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0179.C5740, NewCertificates0179.C5741, NewCertificates0179.C5742, NewCertificates0179.C5743, NewCertificates0179.C5744, NewCertificates0179.C5745, NewCertificates0179.C5746, NewCertificates0179.C5747} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0179.C5748, NewCertificates0179.C5749, NewCertificates0179.C5750, NewCertificates0179.C5751, NewCertificates0179.C5752, NewCertificates0179.C5753, NewCertificates0179.C5754, NewCertificates0179.C5755} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0178.obstruction5724
  · exact NewCertificates0178.obstruction5725
  · exact NewCertificates0178.obstruction5726
  · exact NewCertificates0178.obstruction5727
  · exact NewCertificates0179.obstruction5728
  · exact NewCertificates0179.obstruction5729
  · exact NewCertificates0179.obstruction5730
  · exact NewCertificates0179.obstruction5731
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0179.obstruction5732
  · exact NewCertificates0179.obstruction5733
  · exact NewCertificates0179.obstruction5734
  · exact NewCertificates0179.obstruction5735
  · exact NewCertificates0179.obstruction5736
  · exact NewCertificates0179.obstruction5737
  · exact NewCertificates0179.obstruction5738
  · exact NewCertificates0179.obstruction5739
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0179.obstruction5740
  · exact NewCertificates0179.obstruction5741
  · exact NewCertificates0179.obstruction5742
  · exact NewCertificates0179.obstruction5743
  · exact NewCertificates0179.obstruction5744
  · exact NewCertificates0179.obstruction5745
  · exact NewCertificates0179.obstruction5746
  · exact NewCertificates0179.obstruction5747
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0179.obstruction5748
  · exact NewCertificates0179.obstruction5749
  · exact NewCertificates0179.obstruction5750
  · exact NewCertificates0179.obstruction5751
  · exact NewCertificates0179.obstruction5752
  · exact NewCertificates0179.obstruction5753
  · exact NewCertificates0179.obstruction5754
  · exact NewCertificates0179.obstruction5755
end Nut8.FiniteSupport120
