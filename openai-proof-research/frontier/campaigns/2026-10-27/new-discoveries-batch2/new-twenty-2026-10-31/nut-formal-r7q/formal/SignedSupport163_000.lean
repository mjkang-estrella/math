import SupportData163
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport163
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0239.C7652, NewCertificates0239.C7653, NewCertificates0239.C7654, NewCertificates0239.C7655, NewCertificates0239.C7656, NewCertificates0239.C7657, NewCertificates0239.C7658, NewCertificates0239.C7659, NewCertificates0239.C7660, NewCertificates0239.C7661, NewCertificates0239.C7662, NewCertificates0239.C7663, NewCertificates0239.C7664, NewCertificates0239.C7665, NewCertificates0239.C7666, NewCertificates0239.C7667, NewCertificates0239.C7668, NewCertificates0239.C7669, NewCertificates0239.C7670, NewCertificates0239.C7671, NewCertificates0239.C7672, NewCertificates0239.C7673, NewCertificates0239.C7674, NewCertificates0239.C7675, NewCertificates0239.C7676, NewCertificates0239.C7677, NewCertificates0239.C7678, NewCertificates0239.C7679, NewCertificates0240.C7680, NewCertificates0240.C7681, NewCertificates0240.C7682, NewCertificates0240.C7683} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0239.obstruction7652
  · exact NewCertificates0239.obstruction7653
  · exact NewCertificates0239.obstruction7654
  · exact NewCertificates0239.obstruction7655
  · exact NewCertificates0239.obstruction7656
  · exact NewCertificates0239.obstruction7657
  · exact NewCertificates0239.obstruction7658
  · exact NewCertificates0239.obstruction7659
  · exact NewCertificates0239.obstruction7660
  · exact NewCertificates0239.obstruction7661
  · exact NewCertificates0239.obstruction7662
  · exact NewCertificates0239.obstruction7663
  · exact NewCertificates0239.obstruction7664
  · exact NewCertificates0239.obstruction7665
  · exact NewCertificates0239.obstruction7666
  · exact NewCertificates0239.obstruction7667
  · exact NewCertificates0239.obstruction7668
  · exact NewCertificates0239.obstruction7669
  · exact NewCertificates0239.obstruction7670
  · exact NewCertificates0239.obstruction7671
  · exact NewCertificates0239.obstruction7672
  · exact NewCertificates0239.obstruction7673
  · exact NewCertificates0239.obstruction7674
  · exact NewCertificates0239.obstruction7675
  · exact NewCertificates0239.obstruction7676
  · exact NewCertificates0239.obstruction7677
  · exact NewCertificates0239.obstruction7678
  · exact NewCertificates0239.obstruction7679
  · exact NewCertificates0240.obstruction7680
  · exact NewCertificates0240.obstruction7681
  · exact NewCertificates0240.obstruction7682
  · exact NewCertificates0240.obstruction7683
end Nut8.FiniteSupport163
