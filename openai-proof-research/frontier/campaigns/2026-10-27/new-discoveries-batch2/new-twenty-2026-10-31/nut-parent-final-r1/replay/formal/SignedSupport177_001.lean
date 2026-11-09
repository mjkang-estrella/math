import SupportData177
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport177
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0259.C8292, NewCertificates0259.C8293, NewCertificates0259.C8294, NewCertificates0259.C8295, NewCertificates0259.C8296, NewCertificates0259.C8297, NewCertificates0259.C8298, NewCertificates0259.C8299} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0259.C8300, NewCertificates0259.C8301, NewCertificates0259.C8302, NewCertificates0259.C8303, NewCertificates0259.C8304, NewCertificates0259.C8305, NewCertificates0259.C8306, NewCertificates0259.C8307} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0259.obstruction8292
  · exact NewCertificates0259.obstruction8293
  · exact NewCertificates0259.obstruction8294
  · exact NewCertificates0259.obstruction8295
  · exact NewCertificates0259.obstruction8296
  · exact NewCertificates0259.obstruction8297
  · exact NewCertificates0259.obstruction8298
  · exact NewCertificates0259.obstruction8299
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0259.obstruction8300
  · exact NewCertificates0259.obstruction8301
  · exact NewCertificates0259.obstruction8302
  · exact NewCertificates0259.obstruction8303
  · exact NewCertificates0259.obstruction8304
  · exact NewCertificates0259.obstruction8305
  · exact NewCertificates0259.obstruction8306
  · exact NewCertificates0259.obstruction8307
end Nut8.FiniteSupport177
