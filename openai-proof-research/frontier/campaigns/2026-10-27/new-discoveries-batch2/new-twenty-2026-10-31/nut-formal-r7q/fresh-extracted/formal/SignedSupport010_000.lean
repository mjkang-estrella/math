import SupportData010
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport010
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0015.C480, NewCertificates0015.C481, NewCertificates0015.C482, NewCertificates0015.C483, NewCertificates0015.C484, NewCertificates0015.C485, NewCertificates0015.C486, NewCertificates0015.C487, NewCertificates0015.C488, NewCertificates0015.C489, NewCertificates0015.C490, NewCertificates0015.C491, NewCertificates0015.C492, NewCertificates0015.C493, NewCertificates0015.C494, NewCertificates0015.C495, NewCertificates0015.C496, NewCertificates0015.C497, NewCertificates0015.C498, NewCertificates0015.C499, NewCertificates0015.C500, NewCertificates0015.C501, NewCertificates0015.C502, NewCertificates0015.C503, NewCertificates0015.C504, NewCertificates0015.C505, NewCertificates0015.C506, NewCertificates0015.C507, NewCertificates0015.C508, NewCertificates0015.C509, NewCertificates0015.C510, NewCertificates0015.C511} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0015.obstruction480
  · exact NewCertificates0015.obstruction481
  · exact NewCertificates0015.obstruction482
  · exact NewCertificates0015.obstruction483
  · exact NewCertificates0015.obstruction484
  · exact NewCertificates0015.obstruction485
  · exact NewCertificates0015.obstruction486
  · exact NewCertificates0015.obstruction487
  · exact NewCertificates0015.obstruction488
  · exact NewCertificates0015.obstruction489
  · exact NewCertificates0015.obstruction490
  · exact NewCertificates0015.obstruction491
  · exact NewCertificates0015.obstruction492
  · exact NewCertificates0015.obstruction493
  · exact NewCertificates0015.obstruction494
  · exact NewCertificates0015.obstruction495
  · exact NewCertificates0015.obstruction496
  · exact NewCertificates0015.obstruction497
  · exact NewCertificates0015.obstruction498
  · exact NewCertificates0015.obstruction499
  · exact NewCertificates0015.obstruction500
  · exact NewCertificates0015.obstruction501
  · exact NewCertificates0015.obstruction502
  · exact NewCertificates0015.obstruction503
  · exact NewCertificates0015.obstruction504
  · exact NewCertificates0015.obstruction505
  · exact NewCertificates0015.obstruction506
  · exact NewCertificates0015.obstruction507
  · exact NewCertificates0015.obstruction508
  · exact NewCertificates0015.obstruction509
  · exact NewCertificates0015.obstruction510
  · exact NewCertificates0015.obstruction511
end Nut8.FiniteSupport010
