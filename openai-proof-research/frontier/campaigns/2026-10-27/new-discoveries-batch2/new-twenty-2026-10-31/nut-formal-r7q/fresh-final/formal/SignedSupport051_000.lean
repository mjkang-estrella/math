import SupportData051
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport051
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0077.C2474, NewCertificates0077.C2475, NewCertificates0077.C2476, NewCertificates0077.C2477, NewCertificates0077.C2478, NewCertificates0077.C2479, NewCertificates0077.C2480, NewCertificates0077.C2481, NewCertificates0077.C2482, NewCertificates0077.C2483, NewCertificates0077.C2484, NewCertificates0077.C2485, NewCertificates0077.C2486, NewCertificates0077.C2487, NewCertificates0077.C2488, NewCertificates0077.C2489, NewCertificates0077.C2490, NewCertificates0077.C2491, NewCertificates0077.C2492, NewCertificates0077.C2493, NewCertificates0077.C2494, NewCertificates0077.C2495, NewCertificates0078.C2496, NewCertificates0078.C2497, NewCertificates0078.C2498, NewCertificates0078.C2499, NewCertificates0078.C2500, NewCertificates0078.C2501, NewCertificates0078.C2502, NewCertificates0078.C2503, NewCertificates0078.C2504, NewCertificates0078.C2505} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0078.C2506, NewCertificates0078.C2507, NewCertificates0078.C2508, NewCertificates0078.C2509, NewCertificates0078.C2510, NewCertificates0078.C2511, NewCertificates0078.C2512, NewCertificates0078.C2513, NewCertificates0078.C2514, NewCertificates0078.C2515, NewCertificates0078.C2516, NewCertificates0078.C2517, NewCertificates0078.C2518, NewCertificates0078.C2519, NewCertificates0078.C2520, NewCertificates0078.C2521} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0077.obstruction2474
  · exact NewCertificates0077.obstruction2475
  · exact NewCertificates0077.obstruction2476
  · exact NewCertificates0077.obstruction2477
  · exact NewCertificates0077.obstruction2478
  · exact NewCertificates0077.obstruction2479
  · exact NewCertificates0077.obstruction2480
  · exact NewCertificates0077.obstruction2481
  · exact NewCertificates0077.obstruction2482
  · exact NewCertificates0077.obstruction2483
  · exact NewCertificates0077.obstruction2484
  · exact NewCertificates0077.obstruction2485
  · exact NewCertificates0077.obstruction2486
  · exact NewCertificates0077.obstruction2487
  · exact NewCertificates0077.obstruction2488
  · exact NewCertificates0077.obstruction2489
  · exact NewCertificates0077.obstruction2490
  · exact NewCertificates0077.obstruction2491
  · exact NewCertificates0077.obstruction2492
  · exact NewCertificates0077.obstruction2493
  · exact NewCertificates0077.obstruction2494
  · exact NewCertificates0077.obstruction2495
  · exact NewCertificates0078.obstruction2496
  · exact NewCertificates0078.obstruction2497
  · exact NewCertificates0078.obstruction2498
  · exact NewCertificates0078.obstruction2499
  · exact NewCertificates0078.obstruction2500
  · exact NewCertificates0078.obstruction2501
  · exact NewCertificates0078.obstruction2502
  · exact NewCertificates0078.obstruction2503
  · exact NewCertificates0078.obstruction2504
  · exact NewCertificates0078.obstruction2505
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0078.obstruction2506
  · exact NewCertificates0078.obstruction2507
  · exact NewCertificates0078.obstruction2508
  · exact NewCertificates0078.obstruction2509
  · exact NewCertificates0078.obstruction2510
  · exact NewCertificates0078.obstruction2511
  · exact NewCertificates0078.obstruction2512
  · exact NewCertificates0078.obstruction2513
  · exact NewCertificates0078.obstruction2514
  · exact NewCertificates0078.obstruction2515
  · exact NewCertificates0078.obstruction2516
  · exact NewCertificates0078.obstruction2517
  · exact NewCertificates0078.obstruction2518
  · exact NewCertificates0078.obstruction2519
  · exact NewCertificates0078.obstruction2520
  · exact NewCertificates0078.obstruction2521
end Nut8.FiniteSupport051
