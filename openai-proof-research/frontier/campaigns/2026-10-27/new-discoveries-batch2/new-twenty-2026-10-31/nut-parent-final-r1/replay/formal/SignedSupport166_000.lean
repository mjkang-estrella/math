import SupportData166
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport166
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0242.C7748, NewCertificates0242.C7749, NewCertificates0242.C7750, NewCertificates0242.C7751, NewCertificates0242.C7752, NewCertificates0242.C7753, NewCertificates0242.C7754, NewCertificates0242.C7755, NewCertificates0242.C7756, NewCertificates0242.C7757, NewCertificates0242.C7758, NewCertificates0242.C7759, NewCertificates0242.C7760, NewCertificates0242.C7761, NewCertificates0242.C7762, NewCertificates0242.C7763, NewCertificates0242.C7764, NewCertificates0242.C7765, NewCertificates0242.C7766, NewCertificates0242.C7767, NewCertificates0242.C7768, NewCertificates0242.C7769, NewCertificates0242.C7770, NewCertificates0242.C7771, NewCertificates0242.C7772, NewCertificates0242.C7773, NewCertificates0242.C7774, NewCertificates0242.C7775, NewCertificates0243.C7776, NewCertificates0243.C7777, NewCertificates0243.C7778, NewCertificates0243.C7779} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0242.obstruction7748
  · exact NewCertificates0242.obstruction7749
  · exact NewCertificates0242.obstruction7750
  · exact NewCertificates0242.obstruction7751
  · exact NewCertificates0242.obstruction7752
  · exact NewCertificates0242.obstruction7753
  · exact NewCertificates0242.obstruction7754
  · exact NewCertificates0242.obstruction7755
  · exact NewCertificates0242.obstruction7756
  · exact NewCertificates0242.obstruction7757
  · exact NewCertificates0242.obstruction7758
  · exact NewCertificates0242.obstruction7759
  · exact NewCertificates0242.obstruction7760
  · exact NewCertificates0242.obstruction7761
  · exact NewCertificates0242.obstruction7762
  · exact NewCertificates0242.obstruction7763
  · exact NewCertificates0242.obstruction7764
  · exact NewCertificates0242.obstruction7765
  · exact NewCertificates0242.obstruction7766
  · exact NewCertificates0242.obstruction7767
  · exact NewCertificates0242.obstruction7768
  · exact NewCertificates0242.obstruction7769
  · exact NewCertificates0242.obstruction7770
  · exact NewCertificates0242.obstruction7771
  · exact NewCertificates0242.obstruction7772
  · exact NewCertificates0242.obstruction7773
  · exact NewCertificates0242.obstruction7774
  · exact NewCertificates0242.obstruction7775
  · exact NewCertificates0243.obstruction7776
  · exact NewCertificates0243.obstruction7777
  · exact NewCertificates0243.obstruction7778
  · exact NewCertificates0243.obstruction7779
end Nut8.FiniteSupport166
