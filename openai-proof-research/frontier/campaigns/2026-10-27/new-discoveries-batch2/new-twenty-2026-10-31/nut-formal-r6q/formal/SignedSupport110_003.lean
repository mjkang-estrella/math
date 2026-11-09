import SupportData110
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport110
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0165.C5300, NewCertificates0165.C5301, NewCertificates0165.C5302, NewCertificates0165.C5303} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0165.C5304, NewCertificates0165.C5305, NewCertificates0165.C5306, NewCertificates0165.C5307} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0165.C5308, NewCertificates0165.C5309, NewCertificates0165.C5310, NewCertificates0165.C5311} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5300
  · exact NewCertificates0165.obstruction5301
  · exact NewCertificates0165.obstruction5302
  · exact NewCertificates0165.obstruction5303
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5304
  · exact NewCertificates0165.obstruction5305
  · exact NewCertificates0165.obstruction5306
  · exact NewCertificates0165.obstruction5307
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0165.obstruction5308
  · exact NewCertificates0165.obstruction5309
  · exact NewCertificates0165.obstruction5310
  · exact NewCertificates0165.obstruction5311
end Nut8.FiniteSupport110
