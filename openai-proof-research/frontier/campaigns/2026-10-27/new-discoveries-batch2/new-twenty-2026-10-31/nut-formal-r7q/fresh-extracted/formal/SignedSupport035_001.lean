import SupportData035
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport035
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0058.C1858, NewCertificates0058.C1859, NewCertificates0058.C1860, NewCertificates0058.C1861, NewCertificates0058.C1862, NewCertificates0058.C1863, NewCertificates0058.C1864, NewCertificates0058.C1865} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0058.obstruction1858
  · exact NewCertificates0058.obstruction1859
  · exact NewCertificates0058.obstruction1860
  · exact NewCertificates0058.obstruction1861
  · exact NewCertificates0058.obstruction1862
  · exact NewCertificates0058.obstruction1863
  · exact NewCertificates0058.obstruction1864
  · exact NewCertificates0058.obstruction1865
end Nut8.FiniteSupport035
