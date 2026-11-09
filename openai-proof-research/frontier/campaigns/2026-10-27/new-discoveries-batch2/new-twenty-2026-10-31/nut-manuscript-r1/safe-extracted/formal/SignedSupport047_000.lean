import SupportData047
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport047
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0071.C2298, NewCertificates0071.C2299, NewCertificates0071.C2300, NewCertificates0071.C2301, NewCertificates0071.C2302, NewCertificates0071.C2303, NewCertificates0072.C2304, NewCertificates0072.C2305, NewCertificates0072.C2306, NewCertificates0072.C2307, NewCertificates0072.C2308, NewCertificates0072.C2309, NewCertificates0072.C2310, NewCertificates0072.C2311, NewCertificates0072.C2312, NewCertificates0072.C2313, NewCertificates0072.C2314, NewCertificates0072.C2315, NewCertificates0072.C2316, NewCertificates0072.C2317, NewCertificates0072.C2318, NewCertificates0072.C2319, NewCertificates0072.C2320, NewCertificates0072.C2321, NewCertificates0072.C2322, NewCertificates0072.C2323, NewCertificates0072.C2324, NewCertificates0072.C2325, NewCertificates0072.C2326, NewCertificates0072.C2327, NewCertificates0072.C2328, NewCertificates0072.C2329} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0071.obstruction2298
  · exact NewCertificates0071.obstruction2299
  · exact NewCertificates0071.obstruction2300
  · exact NewCertificates0071.obstruction2301
  · exact NewCertificates0071.obstruction2302
  · exact NewCertificates0071.obstruction2303
  · exact NewCertificates0072.obstruction2304
  · exact NewCertificates0072.obstruction2305
  · exact NewCertificates0072.obstruction2306
  · exact NewCertificates0072.obstruction2307
  · exact NewCertificates0072.obstruction2308
  · exact NewCertificates0072.obstruction2309
  · exact NewCertificates0072.obstruction2310
  · exact NewCertificates0072.obstruction2311
  · exact NewCertificates0072.obstruction2312
  · exact NewCertificates0072.obstruction2313
  · exact NewCertificates0072.obstruction2314
  · exact NewCertificates0072.obstruction2315
  · exact NewCertificates0072.obstruction2316
  · exact NewCertificates0072.obstruction2317
  · exact NewCertificates0072.obstruction2318
  · exact NewCertificates0072.obstruction2319
  · exact NewCertificates0072.obstruction2320
  · exact NewCertificates0072.obstruction2321
  · exact NewCertificates0072.obstruction2322
  · exact NewCertificates0072.obstruction2323
  · exact NewCertificates0072.obstruction2324
  · exact NewCertificates0072.obstruction2325
  · exact NewCertificates0072.obstruction2326
  · exact NewCertificates0072.obstruction2327
  · exact NewCertificates0072.obstruction2328
  · exact NewCertificates0072.obstruction2329
end Nut8.FiniteSupport047
