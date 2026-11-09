import SupportData167
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport167
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0243.C7780, NewCertificates0243.C7781, NewCertificates0243.C7782, NewCertificates0243.C7783, NewCertificates0243.C7784, NewCertificates0243.C7785, NewCertificates0243.C7786, NewCertificates0243.C7787, NewCertificates0243.C7788, NewCertificates0243.C7789, NewCertificates0243.C7790, NewCertificates0243.C7791, NewCertificates0243.C7792, NewCertificates0243.C7793, NewCertificates0243.C7794, NewCertificates0243.C7795} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0243.C7796, NewCertificates0243.C7797, NewCertificates0243.C7798, NewCertificates0243.C7799, NewCertificates0243.C7800, NewCertificates0243.C7801, NewCertificates0243.C7802, NewCertificates0243.C7803} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0243.obstruction7780
  · exact NewCertificates0243.obstruction7781
  · exact NewCertificates0243.obstruction7782
  · exact NewCertificates0243.obstruction7783
  · exact NewCertificates0243.obstruction7784
  · exact NewCertificates0243.obstruction7785
  · exact NewCertificates0243.obstruction7786
  · exact NewCertificates0243.obstruction7787
  · exact NewCertificates0243.obstruction7788
  · exact NewCertificates0243.obstruction7789
  · exact NewCertificates0243.obstruction7790
  · exact NewCertificates0243.obstruction7791
  · exact NewCertificates0243.obstruction7792
  · exact NewCertificates0243.obstruction7793
  · exact NewCertificates0243.obstruction7794
  · exact NewCertificates0243.obstruction7795
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0243.obstruction7796
  · exact NewCertificates0243.obstruction7797
  · exact NewCertificates0243.obstruction7798
  · exact NewCertificates0243.obstruction7799
  · exact NewCertificates0243.obstruction7800
  · exact NewCertificates0243.obstruction7801
  · exact NewCertificates0243.obstruction7802
  · exact NewCertificates0243.obstruction7803
end Nut8.FiniteSupport167
