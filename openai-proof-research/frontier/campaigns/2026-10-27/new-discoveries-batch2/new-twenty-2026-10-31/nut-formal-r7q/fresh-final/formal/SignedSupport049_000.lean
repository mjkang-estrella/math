import SupportData049
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport049
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0074.C2378, NewCertificates0074.C2379, NewCertificates0074.C2380, NewCertificates0074.C2381, NewCertificates0074.C2382, NewCertificates0074.C2383, NewCertificates0074.C2384, NewCertificates0074.C2385, NewCertificates0074.C2386, NewCertificates0074.C2387, NewCertificates0074.C2388, NewCertificates0074.C2389, NewCertificates0074.C2390, NewCertificates0074.C2391, NewCertificates0074.C2392, NewCertificates0074.C2393, NewCertificates0074.C2394, NewCertificates0074.C2395, NewCertificates0074.C2396, NewCertificates0074.C2397, NewCertificates0074.C2398, NewCertificates0074.C2399, NewCertificates0075.C2400, NewCertificates0075.C2401, NewCertificates0075.C2402, NewCertificates0075.C2403, NewCertificates0075.C2404, NewCertificates0075.C2405, NewCertificates0075.C2406, NewCertificates0075.C2407, NewCertificates0075.C2408, NewCertificates0075.C2409} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0075.C2410, NewCertificates0075.C2411, NewCertificates0075.C2412, NewCertificates0075.C2413, NewCertificates0075.C2414, NewCertificates0075.C2415, NewCertificates0075.C2416, NewCertificates0075.C2417, NewCertificates0075.C2418, NewCertificates0075.C2419, NewCertificates0075.C2420, NewCertificates0075.C2421, NewCertificates0075.C2422, NewCertificates0075.C2423, NewCertificates0075.C2424, NewCertificates0075.C2425} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0074.obstruction2378
  · exact NewCertificates0074.obstruction2379
  · exact NewCertificates0074.obstruction2380
  · exact NewCertificates0074.obstruction2381
  · exact NewCertificates0074.obstruction2382
  · exact NewCertificates0074.obstruction2383
  · exact NewCertificates0074.obstruction2384
  · exact NewCertificates0074.obstruction2385
  · exact NewCertificates0074.obstruction2386
  · exact NewCertificates0074.obstruction2387
  · exact NewCertificates0074.obstruction2388
  · exact NewCertificates0074.obstruction2389
  · exact NewCertificates0074.obstruction2390
  · exact NewCertificates0074.obstruction2391
  · exact NewCertificates0074.obstruction2392
  · exact NewCertificates0074.obstruction2393
  · exact NewCertificates0074.obstruction2394
  · exact NewCertificates0074.obstruction2395
  · exact NewCertificates0074.obstruction2396
  · exact NewCertificates0074.obstruction2397
  · exact NewCertificates0074.obstruction2398
  · exact NewCertificates0074.obstruction2399
  · exact NewCertificates0075.obstruction2400
  · exact NewCertificates0075.obstruction2401
  · exact NewCertificates0075.obstruction2402
  · exact NewCertificates0075.obstruction2403
  · exact NewCertificates0075.obstruction2404
  · exact NewCertificates0075.obstruction2405
  · exact NewCertificates0075.obstruction2406
  · exact NewCertificates0075.obstruction2407
  · exact NewCertificates0075.obstruction2408
  · exact NewCertificates0075.obstruction2409
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0075.obstruction2410
  · exact NewCertificates0075.obstruction2411
  · exact NewCertificates0075.obstruction2412
  · exact NewCertificates0075.obstruction2413
  · exact NewCertificates0075.obstruction2414
  · exact NewCertificates0075.obstruction2415
  · exact NewCertificates0075.obstruction2416
  · exact NewCertificates0075.obstruction2417
  · exact NewCertificates0075.obstruction2418
  · exact NewCertificates0075.obstruction2419
  · exact NewCertificates0075.obstruction2420
  · exact NewCertificates0075.obstruction2421
  · exact NewCertificates0075.obstruction2422
  · exact NewCertificates0075.obstruction2423
  · exact NewCertificates0075.obstruction2424
  · exact NewCertificates0075.obstruction2425
end Nut8.FiniteSupport049
