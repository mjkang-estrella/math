import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0052.C1672, NewCertificates0052.C1673, NewCertificates0052.C1674, NewCertificates0052.C1675, NewCertificates0052.C1676, NewCertificates0052.C1677, NewCertificates0052.C1678, NewCertificates0052.C1679} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0052.C1680, NewCertificates0052.C1681, NewCertificates0052.C1682, NewCertificates0052.C1683} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0052.C1684, NewCertificates0052.C1685, NewCertificates0052.C1686, NewCertificates0052.C1687, NewCertificates0052.C1688, NewCertificates0052.C1689, NewCertificates0052.C1690, NewCertificates0052.C1691} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0052.C1692, NewCertificates0052.C1693, NewCertificates0052.C1694, NewCertificates0052.C1695, NewCertificates0053.C1696, NewCertificates0053.C1697, NewCertificates0053.C1698, NewCertificates0053.C1699} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0052.obstruction1672
  · exact NewCertificates0052.obstruction1673
  · exact NewCertificates0052.obstruction1674
  · exact NewCertificates0052.obstruction1675
  · exact NewCertificates0052.obstruction1676
  · exact NewCertificates0052.obstruction1677
  · exact NewCertificates0052.obstruction1678
  · exact NewCertificates0052.obstruction1679
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0052.obstruction1680
  · exact NewCertificates0052.obstruction1681
  · exact NewCertificates0052.obstruction1682
  · exact NewCertificates0052.obstruction1683
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0052.obstruction1684
  · exact NewCertificates0052.obstruction1685
  · exact NewCertificates0052.obstruction1686
  · exact NewCertificates0052.obstruction1687
  · exact NewCertificates0052.obstruction1688
  · exact NewCertificates0052.obstruction1689
  · exact NewCertificates0052.obstruction1690
  · exact NewCertificates0052.obstruction1691
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0052.obstruction1692
  · exact NewCertificates0052.obstruction1693
  · exact NewCertificates0052.obstruction1694
  · exact NewCertificates0052.obstruction1695
  · exact NewCertificates0053.obstruction1696
  · exact NewCertificates0053.obstruction1697
  · exact NewCertificates0053.obstruction1698
  · exact NewCertificates0053.obstruction1699
end Nut8.FiniteSupport034
