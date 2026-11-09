import SupportData004
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport004
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0006.C192, NewCertificates0006.C193, NewCertificates0006.C194, NewCertificates0006.C195, NewCertificates0006.C196, NewCertificates0006.C197, NewCertificates0006.C198, NewCertificates0006.C199, NewCertificates0006.C200, NewCertificates0006.C201, NewCertificates0006.C202, NewCertificates0006.C203, NewCertificates0006.C204, NewCertificates0006.C205, NewCertificates0006.C206, NewCertificates0006.C207, NewCertificates0006.C208, NewCertificates0006.C209, NewCertificates0006.C210, NewCertificates0006.C211, NewCertificates0006.C212, NewCertificates0006.C213, NewCertificates0006.C214, NewCertificates0006.C215, NewCertificates0006.C216, NewCertificates0006.C217, NewCertificates0006.C218, NewCertificates0006.C219, NewCertificates0006.C220, NewCertificates0006.C221, NewCertificates0006.C222, NewCertificates0006.C223} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0006.obstruction192
  · exact NewCertificates0006.obstruction193
  · exact NewCertificates0006.obstruction194
  · exact NewCertificates0006.obstruction195
  · exact NewCertificates0006.obstruction196
  · exact NewCertificates0006.obstruction197
  · exact NewCertificates0006.obstruction198
  · exact NewCertificates0006.obstruction199
  · exact NewCertificates0006.obstruction200
  · exact NewCertificates0006.obstruction201
  · exact NewCertificates0006.obstruction202
  · exact NewCertificates0006.obstruction203
  · exact NewCertificates0006.obstruction204
  · exact NewCertificates0006.obstruction205
  · exact NewCertificates0006.obstruction206
  · exact NewCertificates0006.obstruction207
  · exact NewCertificates0006.obstruction208
  · exact NewCertificates0006.obstruction209
  · exact NewCertificates0006.obstruction210
  · exact NewCertificates0006.obstruction211
  · exact NewCertificates0006.obstruction212
  · exact NewCertificates0006.obstruction213
  · exact NewCertificates0006.obstruction214
  · exact NewCertificates0006.obstruction215
  · exact NewCertificates0006.obstruction216
  · exact NewCertificates0006.obstruction217
  · exact NewCertificates0006.obstruction218
  · exact NewCertificates0006.obstruction219
  · exact NewCertificates0006.obstruction220
  · exact NewCertificates0006.obstruction221
  · exact NewCertificates0006.obstruction222
  · exact NewCertificates0006.obstruction223
end Nut8.FiniteSupport004
