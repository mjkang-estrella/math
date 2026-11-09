import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration16 : signedPatterns (U16.submatrix e e) p = {NewCertificates0053.C1724, NewCertificates0053.C1725, NewCertificates0053.C1726, NewCertificates0053.C1727, NewCertificates0054.C1728, NewCertificates0054.C1729, NewCertificates0054.C1730, NewCertificates0054.C1731} := by
  decide +kernel
theorem signed_enumeration17 : signedPatterns (U17.submatrix e e) p = {NewCertificates0054.C1732, NewCertificates0054.C1733, NewCertificates0054.C1734, NewCertificates0054.C1735} := by
  decide +kernel
theorem signed_enumeration18 : signedPatterns (U18.submatrix e e) p = {NewCertificates0054.C1736, NewCertificates0054.C1737, NewCertificates0054.C1738, NewCertificates0054.C1739, NewCertificates0054.C1740, NewCertificates0054.C1741, NewCertificates0054.C1742, NewCertificates0054.C1743} := by
  decide +kernel
theorem signed_enumeration19 : signedPatterns (U19.submatrix e e) p = {NewCertificates0054.C1744, NewCertificates0054.C1745, NewCertificates0054.C1746, NewCertificates0054.C1747} := by
  decide +kernel
theorem checked16 : ∀ A ∈ signedPatterns (U16.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration16]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0053.obstruction1724
  · exact NewCertificates0053.obstruction1725
  · exact NewCertificates0053.obstruction1726
  · exact NewCertificates0053.obstruction1727
  · exact NewCertificates0054.obstruction1728
  · exact NewCertificates0054.obstruction1729
  · exact NewCertificates0054.obstruction1730
  · exact NewCertificates0054.obstruction1731
theorem checked17 : ∀ A ∈ signedPatterns (U17.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration17]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1732
  · exact NewCertificates0054.obstruction1733
  · exact NewCertificates0054.obstruction1734
  · exact NewCertificates0054.obstruction1735
theorem checked18 : ∀ A ∈ signedPatterns (U18.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration18]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1736
  · exact NewCertificates0054.obstruction1737
  · exact NewCertificates0054.obstruction1738
  · exact NewCertificates0054.obstruction1739
  · exact NewCertificates0054.obstruction1740
  · exact NewCertificates0054.obstruction1741
  · exact NewCertificates0054.obstruction1742
  · exact NewCertificates0054.obstruction1743
theorem checked19 : ∀ A ∈ signedPatterns (U19.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration19]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0054.obstruction1744
  · exact NewCertificates0054.obstruction1745
  · exact NewCertificates0054.obstruction1746
  · exact NewCertificates0054.obstruction1747
end Nut8.FiniteSupport034
