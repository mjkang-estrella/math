import SupportData164
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport164
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0240.C7684, NewCertificates0240.C7685, NewCertificates0240.C7686, NewCertificates0240.C7687, NewCertificates0240.C7688, NewCertificates0240.C7689, NewCertificates0240.C7690, NewCertificates0240.C7691, NewCertificates0240.C7692, NewCertificates0240.C7693, NewCertificates0240.C7694, NewCertificates0240.C7695, NewCertificates0240.C7696, NewCertificates0240.C7697, NewCertificates0240.C7698, NewCertificates0240.C7699, NewCertificates0240.C7700, NewCertificates0240.C7701, NewCertificates0240.C7702, NewCertificates0240.C7703, NewCertificates0240.C7704, NewCertificates0240.C7705, NewCertificates0240.C7706, NewCertificates0240.C7707, NewCertificates0240.C7708, NewCertificates0240.C7709, NewCertificates0240.C7710, NewCertificates0240.C7711, NewCertificates0241.C7712, NewCertificates0241.C7713, NewCertificates0241.C7714, NewCertificates0241.C7715} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0240.obstruction7684
  · exact NewCertificates0240.obstruction7685
  · exact NewCertificates0240.obstruction7686
  · exact NewCertificates0240.obstruction7687
  · exact NewCertificates0240.obstruction7688
  · exact NewCertificates0240.obstruction7689
  · exact NewCertificates0240.obstruction7690
  · exact NewCertificates0240.obstruction7691
  · exact NewCertificates0240.obstruction7692
  · exact NewCertificates0240.obstruction7693
  · exact NewCertificates0240.obstruction7694
  · exact NewCertificates0240.obstruction7695
  · exact NewCertificates0240.obstruction7696
  · exact NewCertificates0240.obstruction7697
  · exact NewCertificates0240.obstruction7698
  · exact NewCertificates0240.obstruction7699
  · exact NewCertificates0240.obstruction7700
  · exact NewCertificates0240.obstruction7701
  · exact NewCertificates0240.obstruction7702
  · exact NewCertificates0240.obstruction7703
  · exact NewCertificates0240.obstruction7704
  · exact NewCertificates0240.obstruction7705
  · exact NewCertificates0240.obstruction7706
  · exact NewCertificates0240.obstruction7707
  · exact NewCertificates0240.obstruction7708
  · exact NewCertificates0240.obstruction7709
  · exact NewCertificates0240.obstruction7710
  · exact NewCertificates0240.obstruction7711
  · exact NewCertificates0241.obstruction7712
  · exact NewCertificates0241.obstruction7713
  · exact NewCertificates0241.obstruction7714
  · exact NewCertificates0241.obstruction7715
end Nut8.FiniteSupport164
