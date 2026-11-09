import SupportData012
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport012
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0017.C560, NewCertificates0017.C561, NewCertificates0017.C562, NewCertificates0017.C563, NewCertificates0017.C564, NewCertificates0017.C565, NewCertificates0017.C566, NewCertificates0017.C567, NewCertificates0017.C568, NewCertificates0017.C569, NewCertificates0017.C570, NewCertificates0017.C571, NewCertificates0017.C572, NewCertificates0017.C573, NewCertificates0017.C574, NewCertificates0017.C575, NewCertificates0018.C576, NewCertificates0018.C577, NewCertificates0018.C578, NewCertificates0018.C579, NewCertificates0018.C580, NewCertificates0018.C581, NewCertificates0018.C582, NewCertificates0018.C583, NewCertificates0018.C584, NewCertificates0018.C585, NewCertificates0018.C586, NewCertificates0018.C587, NewCertificates0018.C588, NewCertificates0018.C589, NewCertificates0018.C590, NewCertificates0018.C591} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0017.obstruction560
  · exact NewCertificates0017.obstruction561
  · exact NewCertificates0017.obstruction562
  · exact NewCertificates0017.obstruction563
  · exact NewCertificates0017.obstruction564
  · exact NewCertificates0017.obstruction565
  · exact NewCertificates0017.obstruction566
  · exact NewCertificates0017.obstruction567
  · exact NewCertificates0017.obstruction568
  · exact NewCertificates0017.obstruction569
  · exact NewCertificates0017.obstruction570
  · exact NewCertificates0017.obstruction571
  · exact NewCertificates0017.obstruction572
  · exact NewCertificates0017.obstruction573
  · exact NewCertificates0017.obstruction574
  · exact NewCertificates0017.obstruction575
  · exact NewCertificates0018.obstruction576
  · exact NewCertificates0018.obstruction577
  · exact NewCertificates0018.obstruction578
  · exact NewCertificates0018.obstruction579
  · exact NewCertificates0018.obstruction580
  · exact NewCertificates0018.obstruction581
  · exact NewCertificates0018.obstruction582
  · exact NewCertificates0018.obstruction583
  · exact NewCertificates0018.obstruction584
  · exact NewCertificates0018.obstruction585
  · exact NewCertificates0018.obstruction586
  · exact NewCertificates0018.obstruction587
  · exact NewCertificates0018.obstruction588
  · exact NewCertificates0018.obstruction589
  · exact NewCertificates0018.obstruction590
  · exact NewCertificates0018.obstruction591
end Nut8.FiniteSupport012
