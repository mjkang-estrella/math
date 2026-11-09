import SupportData052
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport052
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0078.C2522, NewCertificates0078.C2523, NewCertificates0078.C2524, NewCertificates0078.C2525, NewCertificates0078.C2526, NewCertificates0078.C2527, NewCertificates0079.C2528, NewCertificates0079.C2529, NewCertificates0079.C2530, NewCertificates0079.C2531, NewCertificates0079.C2532, NewCertificates0079.C2533, NewCertificates0079.C2534, NewCertificates0079.C2535, NewCertificates0079.C2536, NewCertificates0079.C2537, NewCertificates0079.C2538, NewCertificates0079.C2539, NewCertificates0079.C2540, NewCertificates0079.C2541, NewCertificates0079.C2542, NewCertificates0079.C2543, NewCertificates0079.C2544, NewCertificates0079.C2545, NewCertificates0079.C2546, NewCertificates0079.C2547, NewCertificates0079.C2548, NewCertificates0079.C2549, NewCertificates0079.C2550, NewCertificates0079.C2551, NewCertificates0079.C2552, NewCertificates0079.C2553} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0078.obstruction2522
  · exact NewCertificates0078.obstruction2523
  · exact NewCertificates0078.obstruction2524
  · exact NewCertificates0078.obstruction2525
  · exact NewCertificates0078.obstruction2526
  · exact NewCertificates0078.obstruction2527
  · exact NewCertificates0079.obstruction2528
  · exact NewCertificates0079.obstruction2529
  · exact NewCertificates0079.obstruction2530
  · exact NewCertificates0079.obstruction2531
  · exact NewCertificates0079.obstruction2532
  · exact NewCertificates0079.obstruction2533
  · exact NewCertificates0079.obstruction2534
  · exact NewCertificates0079.obstruction2535
  · exact NewCertificates0079.obstruction2536
  · exact NewCertificates0079.obstruction2537
  · exact NewCertificates0079.obstruction2538
  · exact NewCertificates0079.obstruction2539
  · exact NewCertificates0079.obstruction2540
  · exact NewCertificates0079.obstruction2541
  · exact NewCertificates0079.obstruction2542
  · exact NewCertificates0079.obstruction2543
  · exact NewCertificates0079.obstruction2544
  · exact NewCertificates0079.obstruction2545
  · exact NewCertificates0079.obstruction2546
  · exact NewCertificates0079.obstruction2547
  · exact NewCertificates0079.obstruction2548
  · exact NewCertificates0079.obstruction2549
  · exact NewCertificates0079.obstruction2550
  · exact NewCertificates0079.obstruction2551
  · exact NewCertificates0079.obstruction2552
  · exact NewCertificates0079.obstruction2553
end Nut8.FiniteSupport052
