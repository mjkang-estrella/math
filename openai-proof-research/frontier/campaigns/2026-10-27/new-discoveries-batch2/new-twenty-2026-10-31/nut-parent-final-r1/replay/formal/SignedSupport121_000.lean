import SupportData121
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport121
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0180.C5772, NewCertificates0180.C5773, NewCertificates0180.C5774, NewCertificates0180.C5775, NewCertificates0180.C5776, NewCertificates0180.C5777, NewCertificates0180.C5778, NewCertificates0180.C5779, NewCertificates0180.C5780, NewCertificates0180.C5781, NewCertificates0180.C5782, NewCertificates0180.C5783, NewCertificates0180.C5784, NewCertificates0180.C5785, NewCertificates0180.C5786, NewCertificates0180.C5787} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0180.obstruction5772
  · exact NewCertificates0180.obstruction5773
  · exact NewCertificates0180.obstruction5774
  · exact NewCertificates0180.obstruction5775
  · exact NewCertificates0180.obstruction5776
  · exact NewCertificates0180.obstruction5777
  · exact NewCertificates0180.obstruction5778
  · exact NewCertificates0180.obstruction5779
  · exact NewCertificates0180.obstruction5780
  · exact NewCertificates0180.obstruction5781
  · exact NewCertificates0180.obstruction5782
  · exact NewCertificates0180.obstruction5783
  · exact NewCertificates0180.obstruction5784
  · exact NewCertificates0180.obstruction5785
  · exact NewCertificates0180.obstruction5786
  · exact NewCertificates0180.obstruction5787
end Nut8.FiniteSupport121
