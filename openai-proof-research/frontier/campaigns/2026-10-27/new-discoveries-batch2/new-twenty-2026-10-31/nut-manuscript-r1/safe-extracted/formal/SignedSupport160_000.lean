import SupportData160
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport160
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0235.C7540, NewCertificates0235.C7541, NewCertificates0235.C7542, NewCertificates0235.C7543, NewCertificates0235.C7544, NewCertificates0235.C7545, NewCertificates0235.C7546, NewCertificates0235.C7547, NewCertificates0235.C7548, NewCertificates0235.C7549, NewCertificates0235.C7550, NewCertificates0235.C7551, NewCertificates0236.C7552, NewCertificates0236.C7553, NewCertificates0236.C7554, NewCertificates0236.C7555, NewCertificates0236.C7556, NewCertificates0236.C7557, NewCertificates0236.C7558, NewCertificates0236.C7559, NewCertificates0236.C7560, NewCertificates0236.C7561, NewCertificates0236.C7562, NewCertificates0236.C7563, NewCertificates0236.C7564, NewCertificates0236.C7565, NewCertificates0236.C7566, NewCertificates0236.C7567, NewCertificates0236.C7568, NewCertificates0236.C7569, NewCertificates0236.C7570, NewCertificates0236.C7571} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0235.obstruction7540
  · exact NewCertificates0235.obstruction7541
  · exact NewCertificates0235.obstruction7542
  · exact NewCertificates0235.obstruction7543
  · exact NewCertificates0235.obstruction7544
  · exact NewCertificates0235.obstruction7545
  · exact NewCertificates0235.obstruction7546
  · exact NewCertificates0235.obstruction7547
  · exact NewCertificates0235.obstruction7548
  · exact NewCertificates0235.obstruction7549
  · exact NewCertificates0235.obstruction7550
  · exact NewCertificates0235.obstruction7551
  · exact NewCertificates0236.obstruction7552
  · exact NewCertificates0236.obstruction7553
  · exact NewCertificates0236.obstruction7554
  · exact NewCertificates0236.obstruction7555
  · exact NewCertificates0236.obstruction7556
  · exact NewCertificates0236.obstruction7557
  · exact NewCertificates0236.obstruction7558
  · exact NewCertificates0236.obstruction7559
  · exact NewCertificates0236.obstruction7560
  · exact NewCertificates0236.obstruction7561
  · exact NewCertificates0236.obstruction7562
  · exact NewCertificates0236.obstruction7563
  · exact NewCertificates0236.obstruction7564
  · exact NewCertificates0236.obstruction7565
  · exact NewCertificates0236.obstruction7566
  · exact NewCertificates0236.obstruction7567
  · exact NewCertificates0236.obstruction7568
  · exact NewCertificates0236.obstruction7569
  · exact NewCertificates0236.obstruction7570
  · exact NewCertificates0236.obstruction7571
end Nut8.FiniteSupport160
