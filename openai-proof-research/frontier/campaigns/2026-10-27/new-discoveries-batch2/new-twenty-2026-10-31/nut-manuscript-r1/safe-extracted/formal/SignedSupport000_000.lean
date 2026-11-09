import SupportData000
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport000
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0000.C0, NewCertificates0000.C1, NewCertificates0000.C2, NewCertificates0000.C3, NewCertificates0000.C4, NewCertificates0000.C5, NewCertificates0000.C6, NewCertificates0000.C7, NewCertificates0000.C8, NewCertificates0000.C9, NewCertificates0000.C10, NewCertificates0000.C11, NewCertificates0000.C12, NewCertificates0000.C13, NewCertificates0000.C14, NewCertificates0000.C15, NewCertificates0000.C16, NewCertificates0000.C17, NewCertificates0000.C18, NewCertificates0000.C19, NewCertificates0000.C20, NewCertificates0000.C21, NewCertificates0000.C22, NewCertificates0000.C23, NewCertificates0000.C24, NewCertificates0000.C25, NewCertificates0000.C26, NewCertificates0000.C27, NewCertificates0000.C28, NewCertificates0000.C29, NewCertificates0000.C30, NewCertificates0000.C31} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0000.obstruction0
  · exact NewCertificates0000.obstruction1
  · exact NewCertificates0000.obstruction2
  · exact NewCertificates0000.obstruction3
  · exact NewCertificates0000.obstruction4
  · exact NewCertificates0000.obstruction5
  · exact NewCertificates0000.obstruction6
  · exact NewCertificates0000.obstruction7
  · exact NewCertificates0000.obstruction8
  · exact NewCertificates0000.obstruction9
  · exact NewCertificates0000.obstruction10
  · exact NewCertificates0000.obstruction11
  · exact NewCertificates0000.obstruction12
  · exact NewCertificates0000.obstruction13
  · exact NewCertificates0000.obstruction14
  · exact NewCertificates0000.obstruction15
  · exact NewCertificates0000.obstruction16
  · exact NewCertificates0000.obstruction17
  · exact NewCertificates0000.obstruction18
  · exact NewCertificates0000.obstruction19
  · exact NewCertificates0000.obstruction20
  · exact NewCertificates0000.obstruction21
  · exact NewCertificates0000.obstruction22
  · exact NewCertificates0000.obstruction23
  · exact NewCertificates0000.obstruction24
  · exact NewCertificates0000.obstruction25
  · exact NewCertificates0000.obstruction26
  · exact NewCertificates0000.obstruction27
  · exact NewCertificates0000.obstruction28
  · exact NewCertificates0000.obstruction29
  · exact NewCertificates0000.obstruction30
  · exact NewCertificates0000.obstruction31
end Nut8.FiniteSupport000
