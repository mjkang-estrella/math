import SupportData157
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport157
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0233.C7464, NewCertificates0233.C7465, NewCertificates0233.C7466, NewCertificates0233.C7467, NewCertificates0233.C7468, NewCertificates0233.C7469, NewCertificates0233.C7470, NewCertificates0233.C7471} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0233.C7472, NewCertificates0233.C7473, NewCertificates0233.C7474, NewCertificates0233.C7475} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0233.obstruction7464
  · exact NewCertificates0233.obstruction7465
  · exact NewCertificates0233.obstruction7466
  · exact NewCertificates0233.obstruction7467
  · exact NewCertificates0233.obstruction7468
  · exact NewCertificates0233.obstruction7469
  · exact NewCertificates0233.obstruction7470
  · exact NewCertificates0233.obstruction7471
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0233.obstruction7472
  · exact NewCertificates0233.obstruction7473
  · exact NewCertificates0233.obstruction7474
  · exact NewCertificates0233.obstruction7475
end Nut8.FiniteSupport157
