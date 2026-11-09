import SupportData002
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport002
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0002.C80, NewCertificates0002.C81, NewCertificates0002.C82, NewCertificates0002.C83, NewCertificates0002.C84, NewCertificates0002.C85, NewCertificates0002.C86, NewCertificates0002.C87, NewCertificates0002.C88, NewCertificates0002.C89, NewCertificates0002.C90, NewCertificates0002.C91, NewCertificates0002.C92, NewCertificates0002.C93, NewCertificates0002.C94, NewCertificates0002.C95, NewCertificates0003.C96, NewCertificates0003.C97, NewCertificates0003.C98, NewCertificates0003.C99, NewCertificates0003.C100, NewCertificates0003.C101, NewCertificates0003.C102, NewCertificates0003.C103, NewCertificates0003.C104, NewCertificates0003.C105, NewCertificates0003.C106, NewCertificates0003.C107, NewCertificates0003.C108, NewCertificates0003.C109, NewCertificates0003.C110, NewCertificates0003.C111} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0003.C112, NewCertificates0003.C113, NewCertificates0003.C114, NewCertificates0003.C115, NewCertificates0003.C116, NewCertificates0003.C117, NewCertificates0003.C118, NewCertificates0003.C119, NewCertificates0003.C120, NewCertificates0003.C121, NewCertificates0003.C122, NewCertificates0003.C123, NewCertificates0003.C124, NewCertificates0003.C125, NewCertificates0003.C126, NewCertificates0003.C127} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0002.obstruction80
  · exact NewCertificates0002.obstruction81
  · exact NewCertificates0002.obstruction82
  · exact NewCertificates0002.obstruction83
  · exact NewCertificates0002.obstruction84
  · exact NewCertificates0002.obstruction85
  · exact NewCertificates0002.obstruction86
  · exact NewCertificates0002.obstruction87
  · exact NewCertificates0002.obstruction88
  · exact NewCertificates0002.obstruction89
  · exact NewCertificates0002.obstruction90
  · exact NewCertificates0002.obstruction91
  · exact NewCertificates0002.obstruction92
  · exact NewCertificates0002.obstruction93
  · exact NewCertificates0002.obstruction94
  · exact NewCertificates0002.obstruction95
  · exact NewCertificates0003.obstruction96
  · exact NewCertificates0003.obstruction97
  · exact NewCertificates0003.obstruction98
  · exact NewCertificates0003.obstruction99
  · exact NewCertificates0003.obstruction100
  · exact NewCertificates0003.obstruction101
  · exact NewCertificates0003.obstruction102
  · exact NewCertificates0003.obstruction103
  · exact NewCertificates0003.obstruction104
  · exact NewCertificates0003.obstruction105
  · exact NewCertificates0003.obstruction106
  · exact NewCertificates0003.obstruction107
  · exact NewCertificates0003.obstruction108
  · exact NewCertificates0003.obstruction109
  · exact NewCertificates0003.obstruction110
  · exact NewCertificates0003.obstruction111
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0003.obstruction112
  · exact NewCertificates0003.obstruction113
  · exact NewCertificates0003.obstruction114
  · exact NewCertificates0003.obstruction115
  · exact NewCertificates0003.obstruction116
  · exact NewCertificates0003.obstruction117
  · exact NewCertificates0003.obstruction118
  · exact NewCertificates0003.obstruction119
  · exact NewCertificates0003.obstruction120
  · exact NewCertificates0003.obstruction121
  · exact NewCertificates0003.obstruction122
  · exact NewCertificates0003.obstruction123
  · exact NewCertificates0003.obstruction124
  · exact NewCertificates0003.obstruction125
  · exact NewCertificates0003.obstruction126
  · exact NewCertificates0003.obstruction127
end Nut8.FiniteSupport002
