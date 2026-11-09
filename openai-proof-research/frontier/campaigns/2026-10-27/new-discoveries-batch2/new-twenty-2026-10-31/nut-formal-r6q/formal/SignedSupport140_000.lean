import SupportData140
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport140
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0203.C6516, NewCertificates0203.C6517, NewCertificates0203.C6518, NewCertificates0203.C6519, NewCertificates0203.C6520, NewCertificates0203.C6521, NewCertificates0203.C6522, NewCertificates0203.C6523, NewCertificates0203.C6524, NewCertificates0203.C6525, NewCertificates0203.C6526, NewCertificates0203.C6527, NewCertificates0204.C6528, NewCertificates0204.C6529, NewCertificates0204.C6530, NewCertificates0204.C6531, NewCertificates0204.C6532, NewCertificates0204.C6533, NewCertificates0204.C6534, NewCertificates0204.C6535, NewCertificates0204.C6536, NewCertificates0204.C6537, NewCertificates0204.C6538, NewCertificates0204.C6539, NewCertificates0204.C6540, NewCertificates0204.C6541, NewCertificates0204.C6542, NewCertificates0204.C6543, NewCertificates0204.C6544, NewCertificates0204.C6545, NewCertificates0204.C6546, NewCertificates0204.C6547} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0203.obstruction6516
  · exact NewCertificates0203.obstruction6517
  · exact NewCertificates0203.obstruction6518
  · exact NewCertificates0203.obstruction6519
  · exact NewCertificates0203.obstruction6520
  · exact NewCertificates0203.obstruction6521
  · exact NewCertificates0203.obstruction6522
  · exact NewCertificates0203.obstruction6523
  · exact NewCertificates0203.obstruction6524
  · exact NewCertificates0203.obstruction6525
  · exact NewCertificates0203.obstruction6526
  · exact NewCertificates0203.obstruction6527
  · exact NewCertificates0204.obstruction6528
  · exact NewCertificates0204.obstruction6529
  · exact NewCertificates0204.obstruction6530
  · exact NewCertificates0204.obstruction6531
  · exact NewCertificates0204.obstruction6532
  · exact NewCertificates0204.obstruction6533
  · exact NewCertificates0204.obstruction6534
  · exact NewCertificates0204.obstruction6535
  · exact NewCertificates0204.obstruction6536
  · exact NewCertificates0204.obstruction6537
  · exact NewCertificates0204.obstruction6538
  · exact NewCertificates0204.obstruction6539
  · exact NewCertificates0204.obstruction6540
  · exact NewCertificates0204.obstruction6541
  · exact NewCertificates0204.obstruction6542
  · exact NewCertificates0204.obstruction6543
  · exact NewCertificates0204.obstruction6544
  · exact NewCertificates0204.obstruction6545
  · exact NewCertificates0204.obstruction6546
  · exact NewCertificates0204.obstruction6547
end Nut8.FiniteSupport140
