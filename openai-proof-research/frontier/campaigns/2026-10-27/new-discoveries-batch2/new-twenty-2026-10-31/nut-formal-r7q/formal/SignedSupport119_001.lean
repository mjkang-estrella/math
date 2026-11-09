import SupportData119
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport119
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0178.C5708, NewCertificates0178.C5709, NewCertificates0178.C5710, NewCertificates0178.C5711, NewCertificates0178.C5712, NewCertificates0178.C5713, NewCertificates0178.C5714, NewCertificates0178.C5715} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0178.C5716, NewCertificates0178.C5717, NewCertificates0178.C5718, NewCertificates0178.C5719, NewCertificates0178.C5720, NewCertificates0178.C5721, NewCertificates0178.C5722, NewCertificates0178.C5723} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0178.obstruction5708
  · exact NewCertificates0178.obstruction5709
  · exact NewCertificates0178.obstruction5710
  · exact NewCertificates0178.obstruction5711
  · exact NewCertificates0178.obstruction5712
  · exact NewCertificates0178.obstruction5713
  · exact NewCertificates0178.obstruction5714
  · exact NewCertificates0178.obstruction5715
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0178.obstruction5716
  · exact NewCertificates0178.obstruction5717
  · exact NewCertificates0178.obstruction5718
  · exact NewCertificates0178.obstruction5719
  · exact NewCertificates0178.obstruction5720
  · exact NewCertificates0178.obstruction5721
  · exact NewCertificates0178.obstruction5722
  · exact NewCertificates0178.obstruction5723
end Nut8.FiniteSupport119
