import SupportData165
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport165
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0241.C7716, NewCertificates0241.C7717, NewCertificates0241.C7718, NewCertificates0241.C7719, NewCertificates0241.C7720, NewCertificates0241.C7721, NewCertificates0241.C7722, NewCertificates0241.C7723, NewCertificates0241.C7724, NewCertificates0241.C7725, NewCertificates0241.C7726, NewCertificates0241.C7727, NewCertificates0241.C7728, NewCertificates0241.C7729, NewCertificates0241.C7730, NewCertificates0241.C7731, NewCertificates0241.C7732, NewCertificates0241.C7733, NewCertificates0241.C7734, NewCertificates0241.C7735, NewCertificates0241.C7736, NewCertificates0241.C7737, NewCertificates0241.C7738, NewCertificates0241.C7739, NewCertificates0241.C7740, NewCertificates0241.C7741, NewCertificates0241.C7742, NewCertificates0241.C7743, NewCertificates0242.C7744, NewCertificates0242.C7745, NewCertificates0242.C7746, NewCertificates0242.C7747} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0241.obstruction7716
  · exact NewCertificates0241.obstruction7717
  · exact NewCertificates0241.obstruction7718
  · exact NewCertificates0241.obstruction7719
  · exact NewCertificates0241.obstruction7720
  · exact NewCertificates0241.obstruction7721
  · exact NewCertificates0241.obstruction7722
  · exact NewCertificates0241.obstruction7723
  · exact NewCertificates0241.obstruction7724
  · exact NewCertificates0241.obstruction7725
  · exact NewCertificates0241.obstruction7726
  · exact NewCertificates0241.obstruction7727
  · exact NewCertificates0241.obstruction7728
  · exact NewCertificates0241.obstruction7729
  · exact NewCertificates0241.obstruction7730
  · exact NewCertificates0241.obstruction7731
  · exact NewCertificates0241.obstruction7732
  · exact NewCertificates0241.obstruction7733
  · exact NewCertificates0241.obstruction7734
  · exact NewCertificates0241.obstruction7735
  · exact NewCertificates0241.obstruction7736
  · exact NewCertificates0241.obstruction7737
  · exact NewCertificates0241.obstruction7738
  · exact NewCertificates0241.obstruction7739
  · exact NewCertificates0241.obstruction7740
  · exact NewCertificates0241.obstruction7741
  · exact NewCertificates0241.obstruction7742
  · exact NewCertificates0241.obstruction7743
  · exact NewCertificates0242.obstruction7744
  · exact NewCertificates0242.obstruction7745
  · exact NewCertificates0242.obstruction7746
  · exact NewCertificates0242.obstruction7747
end Nut8.FiniteSupport165
