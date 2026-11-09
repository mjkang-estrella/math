import SupportData094
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport094
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0137.C4390, NewCertificates0137.C4391, NewCertificates0137.C4392, NewCertificates0137.C4393, NewCertificates0137.C4394, NewCertificates0137.C4395, NewCertificates0137.C4396, NewCertificates0137.C4397} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0137.obstruction4390
  · exact NewCertificates0137.obstruction4391
  · exact NewCertificates0137.obstruction4392
  · exact NewCertificates0137.obstruction4393
  · exact NewCertificates0137.obstruction4394
  · exact NewCertificates0137.obstruction4395
  · exact NewCertificates0137.obstruction4396
  · exact NewCertificates0137.obstruction4397
end Nut8.FiniteSupport094
