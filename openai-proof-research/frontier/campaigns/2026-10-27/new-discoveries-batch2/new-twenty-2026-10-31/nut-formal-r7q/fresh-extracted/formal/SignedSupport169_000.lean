import SupportData169
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport169
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0245.C7844, NewCertificates0245.C7845, NewCertificates0245.C7846, NewCertificates0245.C7847, NewCertificates0245.C7848, NewCertificates0245.C7849, NewCertificates0245.C7850, NewCertificates0245.C7851, NewCertificates0245.C7852, NewCertificates0245.C7853, NewCertificates0245.C7854, NewCertificates0245.C7855, NewCertificates0245.C7856, NewCertificates0245.C7857, NewCertificates0245.C7858, NewCertificates0245.C7859} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0245.C7860, NewCertificates0245.C7861, NewCertificates0245.C7862, NewCertificates0245.C7863, NewCertificates0245.C7864, NewCertificates0245.C7865, NewCertificates0245.C7866, NewCertificates0245.C7867} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0245.obstruction7844
  · exact NewCertificates0245.obstruction7845
  · exact NewCertificates0245.obstruction7846
  · exact NewCertificates0245.obstruction7847
  · exact NewCertificates0245.obstruction7848
  · exact NewCertificates0245.obstruction7849
  · exact NewCertificates0245.obstruction7850
  · exact NewCertificates0245.obstruction7851
  · exact NewCertificates0245.obstruction7852
  · exact NewCertificates0245.obstruction7853
  · exact NewCertificates0245.obstruction7854
  · exact NewCertificates0245.obstruction7855
  · exact NewCertificates0245.obstruction7856
  · exact NewCertificates0245.obstruction7857
  · exact NewCertificates0245.obstruction7858
  · exact NewCertificates0245.obstruction7859
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0245.obstruction7860
  · exact NewCertificates0245.obstruction7861
  · exact NewCertificates0245.obstruction7862
  · exact NewCertificates0245.obstruction7863
  · exact NewCertificates0245.obstruction7864
  · exact NewCertificates0245.obstruction7865
  · exact NewCertificates0245.obstruction7866
  · exact NewCertificates0245.obstruction7867
end Nut8.FiniteSupport169
