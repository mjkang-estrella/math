import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration28 : signedPatterns (U28.submatrix e e) p = {NewCertificates0184.C5900, NewCertificates0184.C5901, NewCertificates0184.C5902, NewCertificates0184.C5903} := by
  decide +kernel
theorem signed_enumeration29 : signedPatterns (U29.submatrix e e) p = {NewCertificates0184.C5904, NewCertificates0184.C5905, NewCertificates0184.C5906, NewCertificates0184.C5907} := by
  decide +kernel
theorem signed_enumeration30 : signedPatterns (U30.submatrix e e) p = {NewCertificates0184.C5908, NewCertificates0184.C5909, NewCertificates0184.C5910, NewCertificates0184.C5911} := by
  decide +kernel
theorem signed_enumeration31 : signedPatterns (U31.submatrix e e) p = {NewCertificates0184.C5912, NewCertificates0184.C5913, NewCertificates0184.C5914, NewCertificates0184.C5915} := by
  decide +kernel
theorem checked28 : ∀ A ∈ signedPatterns (U28.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration28]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5900
  · exact NewCertificates0184.obstruction5901
  · exact NewCertificates0184.obstruction5902
  · exact NewCertificates0184.obstruction5903
theorem checked29 : ∀ A ∈ signedPatterns (U29.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration29]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5904
  · exact NewCertificates0184.obstruction5905
  · exact NewCertificates0184.obstruction5906
  · exact NewCertificates0184.obstruction5907
theorem checked30 : ∀ A ∈ signedPatterns (U30.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration30]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5908
  · exact NewCertificates0184.obstruction5909
  · exact NewCertificates0184.obstruction5910
  · exact NewCertificates0184.obstruction5911
theorem checked31 : ∀ A ∈ signedPatterns (U31.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration31]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5912
  · exact NewCertificates0184.obstruction5913
  · exact NewCertificates0184.obstruction5914
  · exact NewCertificates0184.obstruction5915
end Nut8.FiniteSupport122
