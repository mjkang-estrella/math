import SupportData045
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport045
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0069.C2234, NewCertificates0069.C2235, NewCertificates0069.C2236, NewCertificates0069.C2237, NewCertificates0069.C2238, NewCertificates0069.C2239, NewCertificates0070.C2240, NewCertificates0070.C2241, NewCertificates0070.C2242, NewCertificates0070.C2243, NewCertificates0070.C2244, NewCertificates0070.C2245, NewCertificates0070.C2246, NewCertificates0070.C2247, NewCertificates0070.C2248, NewCertificates0070.C2249, NewCertificates0070.C2250, NewCertificates0070.C2251, NewCertificates0070.C2252, NewCertificates0070.C2253, NewCertificates0070.C2254, NewCertificates0070.C2255, NewCertificates0070.C2256, NewCertificates0070.C2257, NewCertificates0070.C2258, NewCertificates0070.C2259, NewCertificates0070.C2260, NewCertificates0070.C2261, NewCertificates0070.C2262, NewCertificates0070.C2263, NewCertificates0070.C2264, NewCertificates0070.C2265} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0069.obstruction2234
  · exact NewCertificates0069.obstruction2235
  · exact NewCertificates0069.obstruction2236
  · exact NewCertificates0069.obstruction2237
  · exact NewCertificates0069.obstruction2238
  · exact NewCertificates0069.obstruction2239
  · exact NewCertificates0070.obstruction2240
  · exact NewCertificates0070.obstruction2241
  · exact NewCertificates0070.obstruction2242
  · exact NewCertificates0070.obstruction2243
  · exact NewCertificates0070.obstruction2244
  · exact NewCertificates0070.obstruction2245
  · exact NewCertificates0070.obstruction2246
  · exact NewCertificates0070.obstruction2247
  · exact NewCertificates0070.obstruction2248
  · exact NewCertificates0070.obstruction2249
  · exact NewCertificates0070.obstruction2250
  · exact NewCertificates0070.obstruction2251
  · exact NewCertificates0070.obstruction2252
  · exact NewCertificates0070.obstruction2253
  · exact NewCertificates0070.obstruction2254
  · exact NewCertificates0070.obstruction2255
  · exact NewCertificates0070.obstruction2256
  · exact NewCertificates0070.obstruction2257
  · exact NewCertificates0070.obstruction2258
  · exact NewCertificates0070.obstruction2259
  · exact NewCertificates0070.obstruction2260
  · exact NewCertificates0070.obstruction2261
  · exact NewCertificates0070.obstruction2262
  · exact NewCertificates0070.obstruction2263
  · exact NewCertificates0070.obstruction2264
  · exact NewCertificates0070.obstruction2265
end Nut8.FiniteSupport045
