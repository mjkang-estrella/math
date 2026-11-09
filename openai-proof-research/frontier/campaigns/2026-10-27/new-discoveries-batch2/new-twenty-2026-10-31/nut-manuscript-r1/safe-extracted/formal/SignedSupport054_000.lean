import SupportData054
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport054
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0080.C2586, NewCertificates0080.C2587, NewCertificates0080.C2588, NewCertificates0080.C2589, NewCertificates0080.C2590, NewCertificates0080.C2591, NewCertificates0081.C2592, NewCertificates0081.C2593, NewCertificates0081.C2594, NewCertificates0081.C2595, NewCertificates0081.C2596, NewCertificates0081.C2597, NewCertificates0081.C2598, NewCertificates0081.C2599, NewCertificates0081.C2600, NewCertificates0081.C2601} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0080.obstruction2586
  · exact NewCertificates0080.obstruction2587
  · exact NewCertificates0080.obstruction2588
  · exact NewCertificates0080.obstruction2589
  · exact NewCertificates0080.obstruction2590
  · exact NewCertificates0080.obstruction2591
  · exact NewCertificates0081.obstruction2592
  · exact NewCertificates0081.obstruction2593
  · exact NewCertificates0081.obstruction2594
  · exact NewCertificates0081.obstruction2595
  · exact NewCertificates0081.obstruction2596
  · exact NewCertificates0081.obstruction2597
  · exact NewCertificates0081.obstruction2598
  · exact NewCertificates0081.obstruction2599
  · exact NewCertificates0081.obstruction2600
  · exact NewCertificates0081.obstruction2601
end Nut8.FiniteSupport054
