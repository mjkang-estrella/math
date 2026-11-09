import SupportData113
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport113
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0172.C5508, NewCertificates0172.C5509, NewCertificates0172.C5510, NewCertificates0172.C5511, NewCertificates0172.C5512, NewCertificates0172.C5513, NewCertificates0172.C5514, NewCertificates0172.C5515} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0172.C5516, NewCertificates0172.C5517, NewCertificates0172.C5518, NewCertificates0172.C5519, NewCertificates0172.C5520, NewCertificates0172.C5521, NewCertificates0172.C5522, NewCertificates0172.C5523} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0172.C5524, NewCertificates0172.C5525, NewCertificates0172.C5526, NewCertificates0172.C5527, NewCertificates0172.C5528, NewCertificates0172.C5529, NewCertificates0172.C5530, NewCertificates0172.C5531} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0172.C5532, NewCertificates0172.C5533, NewCertificates0172.C5534, NewCertificates0172.C5535, NewCertificates0173.C5536, NewCertificates0173.C5537, NewCertificates0173.C5538, NewCertificates0173.C5539} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0172.obstruction5508
  · exact NewCertificates0172.obstruction5509
  · exact NewCertificates0172.obstruction5510
  · exact NewCertificates0172.obstruction5511
  · exact NewCertificates0172.obstruction5512
  · exact NewCertificates0172.obstruction5513
  · exact NewCertificates0172.obstruction5514
  · exact NewCertificates0172.obstruction5515
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0172.obstruction5516
  · exact NewCertificates0172.obstruction5517
  · exact NewCertificates0172.obstruction5518
  · exact NewCertificates0172.obstruction5519
  · exact NewCertificates0172.obstruction5520
  · exact NewCertificates0172.obstruction5521
  · exact NewCertificates0172.obstruction5522
  · exact NewCertificates0172.obstruction5523
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0172.obstruction5524
  · exact NewCertificates0172.obstruction5525
  · exact NewCertificates0172.obstruction5526
  · exact NewCertificates0172.obstruction5527
  · exact NewCertificates0172.obstruction5528
  · exact NewCertificates0172.obstruction5529
  · exact NewCertificates0172.obstruction5530
  · exact NewCertificates0172.obstruction5531
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0172.obstruction5532
  · exact NewCertificates0172.obstruction5533
  · exact NewCertificates0172.obstruction5534
  · exact NewCertificates0172.obstruction5535
  · exact NewCertificates0173.obstruction5536
  · exact NewCertificates0173.obstruction5537
  · exact NewCertificates0173.obstruction5538
  · exact NewCertificates0173.obstruction5539
end Nut8.FiniteSupport113
