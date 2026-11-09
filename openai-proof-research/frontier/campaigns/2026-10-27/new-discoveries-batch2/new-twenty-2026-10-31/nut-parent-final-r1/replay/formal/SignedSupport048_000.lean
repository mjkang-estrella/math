import SupportData048
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport048
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0072.C2330, NewCertificates0072.C2331, NewCertificates0072.C2332, NewCertificates0072.C2333, NewCertificates0072.C2334, NewCertificates0072.C2335, NewCertificates0073.C2336, NewCertificates0073.C2337, NewCertificates0073.C2338, NewCertificates0073.C2339, NewCertificates0073.C2340, NewCertificates0073.C2341, NewCertificates0073.C2342, NewCertificates0073.C2343, NewCertificates0073.C2344, NewCertificates0073.C2345, NewCertificates0073.C2346, NewCertificates0073.C2347, NewCertificates0073.C2348, NewCertificates0073.C2349, NewCertificates0073.C2350, NewCertificates0073.C2351, NewCertificates0073.C2352, NewCertificates0073.C2353, NewCertificates0073.C2354, NewCertificates0073.C2355, NewCertificates0073.C2356, NewCertificates0073.C2357, NewCertificates0073.C2358, NewCertificates0073.C2359, NewCertificates0073.C2360, NewCertificates0073.C2361} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0073.C2362, NewCertificates0073.C2363, NewCertificates0073.C2364, NewCertificates0073.C2365, NewCertificates0073.C2366, NewCertificates0073.C2367, NewCertificates0074.C2368, NewCertificates0074.C2369, NewCertificates0074.C2370, NewCertificates0074.C2371, NewCertificates0074.C2372, NewCertificates0074.C2373, NewCertificates0074.C2374, NewCertificates0074.C2375, NewCertificates0074.C2376, NewCertificates0074.C2377} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0072.obstruction2330
  · exact NewCertificates0072.obstruction2331
  · exact NewCertificates0072.obstruction2332
  · exact NewCertificates0072.obstruction2333
  · exact NewCertificates0072.obstruction2334
  · exact NewCertificates0072.obstruction2335
  · exact NewCertificates0073.obstruction2336
  · exact NewCertificates0073.obstruction2337
  · exact NewCertificates0073.obstruction2338
  · exact NewCertificates0073.obstruction2339
  · exact NewCertificates0073.obstruction2340
  · exact NewCertificates0073.obstruction2341
  · exact NewCertificates0073.obstruction2342
  · exact NewCertificates0073.obstruction2343
  · exact NewCertificates0073.obstruction2344
  · exact NewCertificates0073.obstruction2345
  · exact NewCertificates0073.obstruction2346
  · exact NewCertificates0073.obstruction2347
  · exact NewCertificates0073.obstruction2348
  · exact NewCertificates0073.obstruction2349
  · exact NewCertificates0073.obstruction2350
  · exact NewCertificates0073.obstruction2351
  · exact NewCertificates0073.obstruction2352
  · exact NewCertificates0073.obstruction2353
  · exact NewCertificates0073.obstruction2354
  · exact NewCertificates0073.obstruction2355
  · exact NewCertificates0073.obstruction2356
  · exact NewCertificates0073.obstruction2357
  · exact NewCertificates0073.obstruction2358
  · exact NewCertificates0073.obstruction2359
  · exact NewCertificates0073.obstruction2360
  · exact NewCertificates0073.obstruction2361
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0073.obstruction2362
  · exact NewCertificates0073.obstruction2363
  · exact NewCertificates0073.obstruction2364
  · exact NewCertificates0073.obstruction2365
  · exact NewCertificates0073.obstruction2366
  · exact NewCertificates0073.obstruction2367
  · exact NewCertificates0074.obstruction2368
  · exact NewCertificates0074.obstruction2369
  · exact NewCertificates0074.obstruction2370
  · exact NewCertificates0074.obstruction2371
  · exact NewCertificates0074.obstruction2372
  · exact NewCertificates0074.obstruction2373
  · exact NewCertificates0074.obstruction2374
  · exact NewCertificates0074.obstruction2375
  · exact NewCertificates0074.obstruction2376
  · exact NewCertificates0074.obstruction2377
end Nut8.FiniteSupport048
