import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0181.C5804, NewCertificates0181.C5805, NewCertificates0181.C5806, NewCertificates0181.C5807} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0181.C5808, NewCertificates0181.C5809, NewCertificates0181.C5810, NewCertificates0181.C5811} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0181.C5812, NewCertificates0181.C5813, NewCertificates0181.C5814, NewCertificates0181.C5815} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0181.C5816, NewCertificates0181.C5817, NewCertificates0181.C5818, NewCertificates0181.C5819} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5804
  · exact NewCertificates0181.obstruction5805
  · exact NewCertificates0181.obstruction5806
  · exact NewCertificates0181.obstruction5807
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5808
  · exact NewCertificates0181.obstruction5809
  · exact NewCertificates0181.obstruction5810
  · exact NewCertificates0181.obstruction5811
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5812
  · exact NewCertificates0181.obstruction5813
  · exact NewCertificates0181.obstruction5814
  · exact NewCertificates0181.obstruction5815
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5816
  · exact NewCertificates0181.obstruction5817
  · exact NewCertificates0181.obstruction5818
  · exact NewCertificates0181.obstruction5819
end Nut8.FiniteSupport122
