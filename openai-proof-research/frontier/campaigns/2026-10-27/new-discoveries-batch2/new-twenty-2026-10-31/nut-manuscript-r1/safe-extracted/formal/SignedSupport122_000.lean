import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0180.C5788, NewCertificates0180.C5789, NewCertificates0180.C5790, NewCertificates0180.C5791} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0181.C5792, NewCertificates0181.C5793, NewCertificates0181.C5794, NewCertificates0181.C5795} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0181.C5796, NewCertificates0181.C5797, NewCertificates0181.C5798, NewCertificates0181.C5799} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0181.C5800, NewCertificates0181.C5801, NewCertificates0181.C5802, NewCertificates0181.C5803} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0180.obstruction5788
  · exact NewCertificates0180.obstruction5789
  · exact NewCertificates0180.obstruction5790
  · exact NewCertificates0180.obstruction5791
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5792
  · exact NewCertificates0181.obstruction5793
  · exact NewCertificates0181.obstruction5794
  · exact NewCertificates0181.obstruction5795
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5796
  · exact NewCertificates0181.obstruction5797
  · exact NewCertificates0181.obstruction5798
  · exact NewCertificates0181.obstruction5799
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5800
  · exact NewCertificates0181.obstruction5801
  · exact NewCertificates0181.obstruction5802
  · exact NewCertificates0181.obstruction5803
end Nut8.FiniteSupport122
