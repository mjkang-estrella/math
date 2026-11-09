import SupportData057
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport057
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0085.C2734, NewCertificates0085.C2735, NewCertificates0085.C2736, NewCertificates0085.C2737, NewCertificates0085.C2738, NewCertificates0085.C2739, NewCertificates0085.C2740, NewCertificates0085.C2741, NewCertificates0085.C2742, NewCertificates0085.C2743, NewCertificates0085.C2744, NewCertificates0085.C2745, NewCertificates0085.C2746, NewCertificates0085.C2747, NewCertificates0085.C2748, NewCertificates0085.C2749, NewCertificates0085.C2750, NewCertificates0085.C2751, NewCertificates0086.C2752, NewCertificates0086.C2753, NewCertificates0086.C2754, NewCertificates0086.C2755, NewCertificates0086.C2756, NewCertificates0086.C2757, NewCertificates0086.C2758, NewCertificates0086.C2759, NewCertificates0086.C2760, NewCertificates0086.C2761, NewCertificates0086.C2762, NewCertificates0086.C2763, NewCertificates0086.C2764, NewCertificates0086.C2765} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0085.obstruction2734
  · exact NewCertificates0085.obstruction2735
  · exact NewCertificates0085.obstruction2736
  · exact NewCertificates0085.obstruction2737
  · exact NewCertificates0085.obstruction2738
  · exact NewCertificates0085.obstruction2739
  · exact NewCertificates0085.obstruction2740
  · exact NewCertificates0085.obstruction2741
  · exact NewCertificates0085.obstruction2742
  · exact NewCertificates0085.obstruction2743
  · exact NewCertificates0085.obstruction2744
  · exact NewCertificates0085.obstruction2745
  · exact NewCertificates0085.obstruction2746
  · exact NewCertificates0085.obstruction2747
  · exact NewCertificates0085.obstruction2748
  · exact NewCertificates0085.obstruction2749
  · exact NewCertificates0085.obstruction2750
  · exact NewCertificates0085.obstruction2751
  · exact NewCertificates0086.obstruction2752
  · exact NewCertificates0086.obstruction2753
  · exact NewCertificates0086.obstruction2754
  · exact NewCertificates0086.obstruction2755
  · exact NewCertificates0086.obstruction2756
  · exact NewCertificates0086.obstruction2757
  · exact NewCertificates0086.obstruction2758
  · exact NewCertificates0086.obstruction2759
  · exact NewCertificates0086.obstruction2760
  · exact NewCertificates0086.obstruction2761
  · exact NewCertificates0086.obstruction2762
  · exact NewCertificates0086.obstruction2763
  · exact NewCertificates0086.obstruction2764
  · exact NewCertificates0086.obstruction2765
end Nut8.FiniteSupport057
