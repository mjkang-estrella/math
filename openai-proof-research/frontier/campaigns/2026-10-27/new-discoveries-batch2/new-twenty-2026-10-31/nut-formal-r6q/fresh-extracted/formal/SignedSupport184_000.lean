import SupportData184
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport184
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0270.C8668, NewCertificates0270.C8669, NewCertificates0270.C8670, NewCertificates0270.C8671, NewCertificates0271.C8672, NewCertificates0271.C8673, NewCertificates0271.C8674, NewCertificates0271.C8675, NewCertificates0271.C8676, NewCertificates0271.C8677, NewCertificates0271.C8678, NewCertificates0271.C8679, NewCertificates0271.C8680, NewCertificates0271.C8681, NewCertificates0271.C8682, NewCertificates0271.C8683, NewCertificates0271.C8684, NewCertificates0271.C8685, NewCertificates0271.C8686, NewCertificates0271.C8687, NewCertificates0271.C8688, NewCertificates0271.C8689, NewCertificates0271.C8690, NewCertificates0271.C8691, NewCertificates0271.C8692, NewCertificates0271.C8693, NewCertificates0271.C8694, NewCertificates0271.C8695, NewCertificates0271.C8696, NewCertificates0271.C8697, NewCertificates0271.C8698, NewCertificates0271.C8699} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0271.C8700, NewCertificates0271.C8701, NewCertificates0271.C8702, NewCertificates0271.C8703, NewCertificates0272.C8704, NewCertificates0272.C8705, NewCertificates0272.C8706, NewCertificates0272.C8707, NewCertificates0272.C8708, NewCertificates0272.C8709, NewCertificates0272.C8710, NewCertificates0272.C8711, NewCertificates0272.C8712, NewCertificates0272.C8713, NewCertificates0272.C8714, NewCertificates0272.C8715} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0270.obstruction8668
  · exact NewCertificates0270.obstruction8669
  · exact NewCertificates0270.obstruction8670
  · exact NewCertificates0270.obstruction8671
  · exact NewCertificates0271.obstruction8672
  · exact NewCertificates0271.obstruction8673
  · exact NewCertificates0271.obstruction8674
  · exact NewCertificates0271.obstruction8675
  · exact NewCertificates0271.obstruction8676
  · exact NewCertificates0271.obstruction8677
  · exact NewCertificates0271.obstruction8678
  · exact NewCertificates0271.obstruction8679
  · exact NewCertificates0271.obstruction8680
  · exact NewCertificates0271.obstruction8681
  · exact NewCertificates0271.obstruction8682
  · exact NewCertificates0271.obstruction8683
  · exact NewCertificates0271.obstruction8684
  · exact NewCertificates0271.obstruction8685
  · exact NewCertificates0271.obstruction8686
  · exact NewCertificates0271.obstruction8687
  · exact NewCertificates0271.obstruction8688
  · exact NewCertificates0271.obstruction8689
  · exact NewCertificates0271.obstruction8690
  · exact NewCertificates0271.obstruction8691
  · exact NewCertificates0271.obstruction8692
  · exact NewCertificates0271.obstruction8693
  · exact NewCertificates0271.obstruction8694
  · exact NewCertificates0271.obstruction8695
  · exact NewCertificates0271.obstruction8696
  · exact NewCertificates0271.obstruction8697
  · exact NewCertificates0271.obstruction8698
  · exact NewCertificates0271.obstruction8699
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0271.obstruction8700
  · exact NewCertificates0271.obstruction8701
  · exact NewCertificates0271.obstruction8702
  · exact NewCertificates0271.obstruction8703
  · exact NewCertificates0272.obstruction8704
  · exact NewCertificates0272.obstruction8705
  · exact NewCertificates0272.obstruction8706
  · exact NewCertificates0272.obstruction8707
  · exact NewCertificates0272.obstruction8708
  · exact NewCertificates0272.obstruction8709
  · exact NewCertificates0272.obstruction8710
  · exact NewCertificates0272.obstruction8711
  · exact NewCertificates0272.obstruction8712
  · exact NewCertificates0272.obstruction8713
  · exact NewCertificates0272.obstruction8714
  · exact NewCertificates0272.obstruction8715
end Nut8.FiniteSupport184
