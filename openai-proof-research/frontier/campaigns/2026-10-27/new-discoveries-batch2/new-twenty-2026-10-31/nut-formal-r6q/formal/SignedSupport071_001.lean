import SupportData071
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport071
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0107.C3446, NewCertificates0107.C3447, NewCertificates0107.C3448, NewCertificates0107.C3449, NewCertificates0107.C3450, NewCertificates0107.C3451, NewCertificates0107.C3452, NewCertificates0107.C3453} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0107.C3454, NewCertificates0107.C3455, NewCertificates0108.C3456, NewCertificates0108.C3457, NewCertificates0108.C3458, NewCertificates0108.C3459, NewCertificates0108.C3460, NewCertificates0108.C3461} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0107.obstruction3446
  · exact NewCertificates0107.obstruction3447
  · exact NewCertificates0107.obstruction3448
  · exact NewCertificates0107.obstruction3449
  · exact NewCertificates0107.obstruction3450
  · exact NewCertificates0107.obstruction3451
  · exact NewCertificates0107.obstruction3452
  · exact NewCertificates0107.obstruction3453
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0107.obstruction3454
  · exact NewCertificates0107.obstruction3455
  · exact NewCertificates0108.obstruction3456
  · exact NewCertificates0108.obstruction3457
  · exact NewCertificates0108.obstruction3458
  · exact NewCertificates0108.obstruction3459
  · exact NewCertificates0108.obstruction3460
  · exact NewCertificates0108.obstruction3461
end Nut8.FiniteSupport071
