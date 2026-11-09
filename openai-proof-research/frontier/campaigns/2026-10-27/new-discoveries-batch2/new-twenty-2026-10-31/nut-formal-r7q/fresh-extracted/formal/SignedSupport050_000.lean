import SupportData050
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport050
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0075.C2426, NewCertificates0075.C2427, NewCertificates0075.C2428, NewCertificates0075.C2429, NewCertificates0075.C2430, NewCertificates0075.C2431, NewCertificates0076.C2432, NewCertificates0076.C2433, NewCertificates0076.C2434, NewCertificates0076.C2435, NewCertificates0076.C2436, NewCertificates0076.C2437, NewCertificates0076.C2438, NewCertificates0076.C2439, NewCertificates0076.C2440, NewCertificates0076.C2441, NewCertificates0076.C2442, NewCertificates0076.C2443, NewCertificates0076.C2444, NewCertificates0076.C2445, NewCertificates0076.C2446, NewCertificates0076.C2447, NewCertificates0076.C2448, NewCertificates0076.C2449, NewCertificates0076.C2450, NewCertificates0076.C2451, NewCertificates0076.C2452, NewCertificates0076.C2453, NewCertificates0076.C2454, NewCertificates0076.C2455, NewCertificates0076.C2456, NewCertificates0076.C2457} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0076.C2458, NewCertificates0076.C2459, NewCertificates0076.C2460, NewCertificates0076.C2461, NewCertificates0076.C2462, NewCertificates0076.C2463, NewCertificates0077.C2464, NewCertificates0077.C2465, NewCertificates0077.C2466, NewCertificates0077.C2467, NewCertificates0077.C2468, NewCertificates0077.C2469, NewCertificates0077.C2470, NewCertificates0077.C2471, NewCertificates0077.C2472, NewCertificates0077.C2473} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0075.obstruction2426
  · exact NewCertificates0075.obstruction2427
  · exact NewCertificates0075.obstruction2428
  · exact NewCertificates0075.obstruction2429
  · exact NewCertificates0075.obstruction2430
  · exact NewCertificates0075.obstruction2431
  · exact NewCertificates0076.obstruction2432
  · exact NewCertificates0076.obstruction2433
  · exact NewCertificates0076.obstruction2434
  · exact NewCertificates0076.obstruction2435
  · exact NewCertificates0076.obstruction2436
  · exact NewCertificates0076.obstruction2437
  · exact NewCertificates0076.obstruction2438
  · exact NewCertificates0076.obstruction2439
  · exact NewCertificates0076.obstruction2440
  · exact NewCertificates0076.obstruction2441
  · exact NewCertificates0076.obstruction2442
  · exact NewCertificates0076.obstruction2443
  · exact NewCertificates0076.obstruction2444
  · exact NewCertificates0076.obstruction2445
  · exact NewCertificates0076.obstruction2446
  · exact NewCertificates0076.obstruction2447
  · exact NewCertificates0076.obstruction2448
  · exact NewCertificates0076.obstruction2449
  · exact NewCertificates0076.obstruction2450
  · exact NewCertificates0076.obstruction2451
  · exact NewCertificates0076.obstruction2452
  · exact NewCertificates0076.obstruction2453
  · exact NewCertificates0076.obstruction2454
  · exact NewCertificates0076.obstruction2455
  · exact NewCertificates0076.obstruction2456
  · exact NewCertificates0076.obstruction2457
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0076.obstruction2458
  · exact NewCertificates0076.obstruction2459
  · exact NewCertificates0076.obstruction2460
  · exact NewCertificates0076.obstruction2461
  · exact NewCertificates0076.obstruction2462
  · exact NewCertificates0076.obstruction2463
  · exact NewCertificates0077.obstruction2464
  · exact NewCertificates0077.obstruction2465
  · exact NewCertificates0077.obstruction2466
  · exact NewCertificates0077.obstruction2467
  · exact NewCertificates0077.obstruction2468
  · exact NewCertificates0077.obstruction2469
  · exact NewCertificates0077.obstruction2470
  · exact NewCertificates0077.obstruction2471
  · exact NewCertificates0077.obstruction2472
  · exact NewCertificates0077.obstruction2473
end Nut8.FiniteSupport050
