import SupportData015
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport015
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0022.C720, NewCertificates0022.C721, NewCertificates0022.C722, NewCertificates0022.C723, NewCertificates0022.C724, NewCertificates0022.C725, NewCertificates0022.C726, NewCertificates0022.C727, NewCertificates0022.C728, NewCertificates0022.C729, NewCertificates0022.C730, NewCertificates0022.C731, NewCertificates0022.C732, NewCertificates0022.C733, NewCertificates0022.C734, NewCertificates0022.C735, NewCertificates0023.C736, NewCertificates0023.C737, NewCertificates0023.C738, NewCertificates0023.C739, NewCertificates0023.C740, NewCertificates0023.C741, NewCertificates0023.C742, NewCertificates0023.C743, NewCertificates0023.C744, NewCertificates0023.C745, NewCertificates0023.C746, NewCertificates0023.C747, NewCertificates0023.C748, NewCertificates0023.C749, NewCertificates0023.C750, NewCertificates0023.C751} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0022.obstruction720
  · exact NewCertificates0022.obstruction721
  · exact NewCertificates0022.obstruction722
  · exact NewCertificates0022.obstruction723
  · exact NewCertificates0022.obstruction724
  · exact NewCertificates0022.obstruction725
  · exact NewCertificates0022.obstruction726
  · exact NewCertificates0022.obstruction727
  · exact NewCertificates0022.obstruction728
  · exact NewCertificates0022.obstruction729
  · exact NewCertificates0022.obstruction730
  · exact NewCertificates0022.obstruction731
  · exact NewCertificates0022.obstruction732
  · exact NewCertificates0022.obstruction733
  · exact NewCertificates0022.obstruction734
  · exact NewCertificates0022.obstruction735
  · exact NewCertificates0023.obstruction736
  · exact NewCertificates0023.obstruction737
  · exact NewCertificates0023.obstruction738
  · exact NewCertificates0023.obstruction739
  · exact NewCertificates0023.obstruction740
  · exact NewCertificates0023.obstruction741
  · exact NewCertificates0023.obstruction742
  · exact NewCertificates0023.obstruction743
  · exact NewCertificates0023.obstruction744
  · exact NewCertificates0023.obstruction745
  · exact NewCertificates0023.obstruction746
  · exact NewCertificates0023.obstruction747
  · exact NewCertificates0023.obstruction748
  · exact NewCertificates0023.obstruction749
  · exact NewCertificates0023.obstruction750
  · exact NewCertificates0023.obstruction751
end Nut8.FiniteSupport015
