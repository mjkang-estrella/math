import SupportData139
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport139
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0202.C6484, NewCertificates0202.C6485, NewCertificates0202.C6486, NewCertificates0202.C6487, NewCertificates0202.C6488, NewCertificates0202.C6489, NewCertificates0202.C6490, NewCertificates0202.C6491, NewCertificates0202.C6492, NewCertificates0202.C6493, NewCertificates0202.C6494, NewCertificates0202.C6495, NewCertificates0203.C6496, NewCertificates0203.C6497, NewCertificates0203.C6498, NewCertificates0203.C6499, NewCertificates0203.C6500, NewCertificates0203.C6501, NewCertificates0203.C6502, NewCertificates0203.C6503, NewCertificates0203.C6504, NewCertificates0203.C6505, NewCertificates0203.C6506, NewCertificates0203.C6507, NewCertificates0203.C6508, NewCertificates0203.C6509, NewCertificates0203.C6510, NewCertificates0203.C6511, NewCertificates0203.C6512, NewCertificates0203.C6513, NewCertificates0203.C6514, NewCertificates0203.C6515} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0202.obstruction6484
  · exact NewCertificates0202.obstruction6485
  · exact NewCertificates0202.obstruction6486
  · exact NewCertificates0202.obstruction6487
  · exact NewCertificates0202.obstruction6488
  · exact NewCertificates0202.obstruction6489
  · exact NewCertificates0202.obstruction6490
  · exact NewCertificates0202.obstruction6491
  · exact NewCertificates0202.obstruction6492
  · exact NewCertificates0202.obstruction6493
  · exact NewCertificates0202.obstruction6494
  · exact NewCertificates0202.obstruction6495
  · exact NewCertificates0203.obstruction6496
  · exact NewCertificates0203.obstruction6497
  · exact NewCertificates0203.obstruction6498
  · exact NewCertificates0203.obstruction6499
  · exact NewCertificates0203.obstruction6500
  · exact NewCertificates0203.obstruction6501
  · exact NewCertificates0203.obstruction6502
  · exact NewCertificates0203.obstruction6503
  · exact NewCertificates0203.obstruction6504
  · exact NewCertificates0203.obstruction6505
  · exact NewCertificates0203.obstruction6506
  · exact NewCertificates0203.obstruction6507
  · exact NewCertificates0203.obstruction6508
  · exact NewCertificates0203.obstruction6509
  · exact NewCertificates0203.obstruction6510
  · exact NewCertificates0203.obstruction6511
  · exact NewCertificates0203.obstruction6512
  · exact NewCertificates0203.obstruction6513
  · exact NewCertificates0203.obstruction6514
  · exact NewCertificates0203.obstruction6515
end Nut8.FiniteSupport139
