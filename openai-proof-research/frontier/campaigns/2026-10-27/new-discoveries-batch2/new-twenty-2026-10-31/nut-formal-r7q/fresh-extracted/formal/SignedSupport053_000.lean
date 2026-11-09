import SupportData053
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport053
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0079.C2554, NewCertificates0079.C2555, NewCertificates0079.C2556, NewCertificates0079.C2557, NewCertificates0079.C2558, NewCertificates0079.C2559, NewCertificates0080.C2560, NewCertificates0080.C2561, NewCertificates0080.C2562, NewCertificates0080.C2563, NewCertificates0080.C2564, NewCertificates0080.C2565, NewCertificates0080.C2566, NewCertificates0080.C2567, NewCertificates0080.C2568, NewCertificates0080.C2569} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0080.C2570, NewCertificates0080.C2571, NewCertificates0080.C2572, NewCertificates0080.C2573, NewCertificates0080.C2574, NewCertificates0080.C2575, NewCertificates0080.C2576, NewCertificates0080.C2577, NewCertificates0080.C2578, NewCertificates0080.C2579, NewCertificates0080.C2580, NewCertificates0080.C2581, NewCertificates0080.C2582, NewCertificates0080.C2583, NewCertificates0080.C2584, NewCertificates0080.C2585} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0079.obstruction2554
  · exact NewCertificates0079.obstruction2555
  · exact NewCertificates0079.obstruction2556
  · exact NewCertificates0079.obstruction2557
  · exact NewCertificates0079.obstruction2558
  · exact NewCertificates0079.obstruction2559
  · exact NewCertificates0080.obstruction2560
  · exact NewCertificates0080.obstruction2561
  · exact NewCertificates0080.obstruction2562
  · exact NewCertificates0080.obstruction2563
  · exact NewCertificates0080.obstruction2564
  · exact NewCertificates0080.obstruction2565
  · exact NewCertificates0080.obstruction2566
  · exact NewCertificates0080.obstruction2567
  · exact NewCertificates0080.obstruction2568
  · exact NewCertificates0080.obstruction2569
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0080.obstruction2570
  · exact NewCertificates0080.obstruction2571
  · exact NewCertificates0080.obstruction2572
  · exact NewCertificates0080.obstruction2573
  · exact NewCertificates0080.obstruction2574
  · exact NewCertificates0080.obstruction2575
  · exact NewCertificates0080.obstruction2576
  · exact NewCertificates0080.obstruction2577
  · exact NewCertificates0080.obstruction2578
  · exact NewCertificates0080.obstruction2579
  · exact NewCertificates0080.obstruction2580
  · exact NewCertificates0080.obstruction2581
  · exact NewCertificates0080.obstruction2582
  · exact NewCertificates0080.obstruction2583
  · exact NewCertificates0080.obstruction2584
  · exact NewCertificates0080.obstruction2585
end Nut8.FiniteSupport053
