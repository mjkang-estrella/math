import SupportData046
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport046
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0070.C2266, NewCertificates0070.C2267, NewCertificates0070.C2268, NewCertificates0070.C2269, NewCertificates0070.C2270, NewCertificates0070.C2271, NewCertificates0071.C2272, NewCertificates0071.C2273, NewCertificates0071.C2274, NewCertificates0071.C2275, NewCertificates0071.C2276, NewCertificates0071.C2277, NewCertificates0071.C2278, NewCertificates0071.C2279, NewCertificates0071.C2280, NewCertificates0071.C2281, NewCertificates0071.C2282, NewCertificates0071.C2283, NewCertificates0071.C2284, NewCertificates0071.C2285, NewCertificates0071.C2286, NewCertificates0071.C2287, NewCertificates0071.C2288, NewCertificates0071.C2289, NewCertificates0071.C2290, NewCertificates0071.C2291, NewCertificates0071.C2292, NewCertificates0071.C2293, NewCertificates0071.C2294, NewCertificates0071.C2295, NewCertificates0071.C2296, NewCertificates0071.C2297} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0070.obstruction2266
  · exact NewCertificates0070.obstruction2267
  · exact NewCertificates0070.obstruction2268
  · exact NewCertificates0070.obstruction2269
  · exact NewCertificates0070.obstruction2270
  · exact NewCertificates0070.obstruction2271
  · exact NewCertificates0071.obstruction2272
  · exact NewCertificates0071.obstruction2273
  · exact NewCertificates0071.obstruction2274
  · exact NewCertificates0071.obstruction2275
  · exact NewCertificates0071.obstruction2276
  · exact NewCertificates0071.obstruction2277
  · exact NewCertificates0071.obstruction2278
  · exact NewCertificates0071.obstruction2279
  · exact NewCertificates0071.obstruction2280
  · exact NewCertificates0071.obstruction2281
  · exact NewCertificates0071.obstruction2282
  · exact NewCertificates0071.obstruction2283
  · exact NewCertificates0071.obstruction2284
  · exact NewCertificates0071.obstruction2285
  · exact NewCertificates0071.obstruction2286
  · exact NewCertificates0071.obstruction2287
  · exact NewCertificates0071.obstruction2288
  · exact NewCertificates0071.obstruction2289
  · exact NewCertificates0071.obstruction2290
  · exact NewCertificates0071.obstruction2291
  · exact NewCertificates0071.obstruction2292
  · exact NewCertificates0071.obstruction2293
  · exact NewCertificates0071.obstruction2294
  · exact NewCertificates0071.obstruction2295
  · exact NewCertificates0071.obstruction2296
  · exact NewCertificates0071.obstruction2297
end Nut8.FiniteSupport046
