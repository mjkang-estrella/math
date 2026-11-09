import SupportData182
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport182
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0269.C8612, NewCertificates0269.C8613, NewCertificates0269.C8614, NewCertificates0269.C8615, NewCertificates0269.C8616, NewCertificates0269.C8617, NewCertificates0269.C8618, NewCertificates0269.C8619} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0269.obstruction8612
  · exact NewCertificates0269.obstruction8613
  · exact NewCertificates0269.obstruction8614
  · exact NewCertificates0269.obstruction8615
  · exact NewCertificates0269.obstruction8616
  · exact NewCertificates0269.obstruction8617
  · exact NewCertificates0269.obstruction8618
  · exact NewCertificates0269.obstruction8619
end Nut8.FiniteSupport182
