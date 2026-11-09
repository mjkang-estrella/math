import SupportData141
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport141
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0204.C6548, NewCertificates0204.C6549, NewCertificates0204.C6550, NewCertificates0204.C6551, NewCertificates0204.C6552, NewCertificates0204.C6553, NewCertificates0204.C6554, NewCertificates0204.C6555, NewCertificates0204.C6556, NewCertificates0204.C6557, NewCertificates0204.C6558, NewCertificates0204.C6559, NewCertificates0205.C6560, NewCertificates0205.C6561, NewCertificates0205.C6562, NewCertificates0205.C6563, NewCertificates0205.C6564, NewCertificates0205.C6565, NewCertificates0205.C6566, NewCertificates0205.C6567, NewCertificates0205.C6568, NewCertificates0205.C6569, NewCertificates0205.C6570, NewCertificates0205.C6571, NewCertificates0205.C6572, NewCertificates0205.C6573, NewCertificates0205.C6574, NewCertificates0205.C6575, NewCertificates0205.C6576, NewCertificates0205.C6577, NewCertificates0205.C6578, NewCertificates0205.C6579} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0204.obstruction6548
  · exact NewCertificates0204.obstruction6549
  · exact NewCertificates0204.obstruction6550
  · exact NewCertificates0204.obstruction6551
  · exact NewCertificates0204.obstruction6552
  · exact NewCertificates0204.obstruction6553
  · exact NewCertificates0204.obstruction6554
  · exact NewCertificates0204.obstruction6555
  · exact NewCertificates0204.obstruction6556
  · exact NewCertificates0204.obstruction6557
  · exact NewCertificates0204.obstruction6558
  · exact NewCertificates0204.obstruction6559
  · exact NewCertificates0205.obstruction6560
  · exact NewCertificates0205.obstruction6561
  · exact NewCertificates0205.obstruction6562
  · exact NewCertificates0205.obstruction6563
  · exact NewCertificates0205.obstruction6564
  · exact NewCertificates0205.obstruction6565
  · exact NewCertificates0205.obstruction6566
  · exact NewCertificates0205.obstruction6567
  · exact NewCertificates0205.obstruction6568
  · exact NewCertificates0205.obstruction6569
  · exact NewCertificates0205.obstruction6570
  · exact NewCertificates0205.obstruction6571
  · exact NewCertificates0205.obstruction6572
  · exact NewCertificates0205.obstruction6573
  · exact NewCertificates0205.obstruction6574
  · exact NewCertificates0205.obstruction6575
  · exact NewCertificates0205.obstruction6576
  · exact NewCertificates0205.obstruction6577
  · exact NewCertificates0205.obstruction6578
  · exact NewCertificates0205.obstruction6579
end Nut8.FiniteSupport141
