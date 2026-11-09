import SupportData044
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport044
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0068.C2202, NewCertificates0068.C2203, NewCertificates0068.C2204, NewCertificates0068.C2205, NewCertificates0068.C2206, NewCertificates0068.C2207, NewCertificates0069.C2208, NewCertificates0069.C2209, NewCertificates0069.C2210, NewCertificates0069.C2211, NewCertificates0069.C2212, NewCertificates0069.C2213, NewCertificates0069.C2214, NewCertificates0069.C2215, NewCertificates0069.C2216, NewCertificates0069.C2217, NewCertificates0069.C2218, NewCertificates0069.C2219, NewCertificates0069.C2220, NewCertificates0069.C2221, NewCertificates0069.C2222, NewCertificates0069.C2223, NewCertificates0069.C2224, NewCertificates0069.C2225, NewCertificates0069.C2226, NewCertificates0069.C2227, NewCertificates0069.C2228, NewCertificates0069.C2229, NewCertificates0069.C2230, NewCertificates0069.C2231, NewCertificates0069.C2232, NewCertificates0069.C2233} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0068.obstruction2202
  · exact NewCertificates0068.obstruction2203
  · exact NewCertificates0068.obstruction2204
  · exact NewCertificates0068.obstruction2205
  · exact NewCertificates0068.obstruction2206
  · exact NewCertificates0068.obstruction2207
  · exact NewCertificates0069.obstruction2208
  · exact NewCertificates0069.obstruction2209
  · exact NewCertificates0069.obstruction2210
  · exact NewCertificates0069.obstruction2211
  · exact NewCertificates0069.obstruction2212
  · exact NewCertificates0069.obstruction2213
  · exact NewCertificates0069.obstruction2214
  · exact NewCertificates0069.obstruction2215
  · exact NewCertificates0069.obstruction2216
  · exact NewCertificates0069.obstruction2217
  · exact NewCertificates0069.obstruction2218
  · exact NewCertificates0069.obstruction2219
  · exact NewCertificates0069.obstruction2220
  · exact NewCertificates0069.obstruction2221
  · exact NewCertificates0069.obstruction2222
  · exact NewCertificates0069.obstruction2223
  · exact NewCertificates0069.obstruction2224
  · exact NewCertificates0069.obstruction2225
  · exact NewCertificates0069.obstruction2226
  · exact NewCertificates0069.obstruction2227
  · exact NewCertificates0069.obstruction2228
  · exact NewCertificates0069.obstruction2229
  · exact NewCertificates0069.obstruction2230
  · exact NewCertificates0069.obstruction2231
  · exact NewCertificates0069.obstruction2232
  · exact NewCertificates0069.obstruction2233
end Nut8.FiniteSupport044
