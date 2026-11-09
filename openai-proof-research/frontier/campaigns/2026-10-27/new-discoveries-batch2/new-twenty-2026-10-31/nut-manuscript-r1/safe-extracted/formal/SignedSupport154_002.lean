import SupportData154
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport154
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0228.C7324, NewCertificates0228.C7325, NewCertificates0228.C7326, NewCertificates0228.C7327, NewCertificates0229.C7328, NewCertificates0229.C7329, NewCertificates0229.C7330, NewCertificates0229.C7331} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0229.C7332, NewCertificates0229.C7333, NewCertificates0229.C7334, NewCertificates0229.C7335} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0228.obstruction7324
  · exact NewCertificates0228.obstruction7325
  · exact NewCertificates0228.obstruction7326
  · exact NewCertificates0228.obstruction7327
  · exact NewCertificates0229.obstruction7328
  · exact NewCertificates0229.obstruction7329
  · exact NewCertificates0229.obstruction7330
  · exact NewCertificates0229.obstruction7331
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0229.obstruction7332
  · exact NewCertificates0229.obstruction7333
  · exact NewCertificates0229.obstruction7334
  · exact NewCertificates0229.obstruction7335
end Nut8.FiniteSupport154
