import SupportData176
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport176
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0256.C8220, NewCertificates0256.C8221, NewCertificates0256.C8222, NewCertificates0256.C8223, NewCertificates0257.C8224, NewCertificates0257.C8225, NewCertificates0257.C8226, NewCertificates0257.C8227} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0257.C8228, NewCertificates0257.C8229, NewCertificates0257.C8230, NewCertificates0257.C8231, NewCertificates0257.C8232, NewCertificates0257.C8233, NewCertificates0257.C8234, NewCertificates0257.C8235} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0256.obstruction8220
  · exact NewCertificates0256.obstruction8221
  · exact NewCertificates0256.obstruction8222
  · exact NewCertificates0256.obstruction8223
  · exact NewCertificates0257.obstruction8224
  · exact NewCertificates0257.obstruction8225
  · exact NewCertificates0257.obstruction8226
  · exact NewCertificates0257.obstruction8227
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0257.obstruction8228
  · exact NewCertificates0257.obstruction8229
  · exact NewCertificates0257.obstruction8230
  · exact NewCertificates0257.obstruction8231
  · exact NewCertificates0257.obstruction8232
  · exact NewCertificates0257.obstruction8233
  · exact NewCertificates0257.obstruction8234
  · exact NewCertificates0257.obstruction8235
end Nut8.FiniteSupport176
