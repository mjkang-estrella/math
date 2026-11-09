import SupportData034
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport034
theorem signed_enumeration32 : signedPatterns (U32.submatrix e e) p = {NewCertificates0055.C1788, NewCertificates0055.C1789, NewCertificates0055.C1790, NewCertificates0055.C1791} := by
  decide +kernel
theorem signed_enumeration33 : signedPatterns (U33.submatrix e e) p = {NewCertificates0056.C1792, NewCertificates0056.C1793} := by
  decide +kernel
theorem checked32 : ∀ A ∈ signedPatterns (U32.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration32]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0055.obstruction1788
  · exact NewCertificates0055.obstruction1789
  · exact NewCertificates0055.obstruction1790
  · exact NewCertificates0055.obstruction1791
theorem checked33 : ∀ A ∈ signedPatterns (U33.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration33]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0056.obstruction1792
  · exact NewCertificates0056.obstruction1793
end Nut8.FiniteSupport034
