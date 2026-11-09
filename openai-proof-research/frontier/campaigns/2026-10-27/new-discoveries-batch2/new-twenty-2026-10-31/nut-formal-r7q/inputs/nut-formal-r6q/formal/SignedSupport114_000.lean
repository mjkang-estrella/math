import SupportData114
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport114
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0173.C5548, NewCertificates0173.C5549, NewCertificates0173.C5550, NewCertificates0173.C5551, NewCertificates0173.C5552, NewCertificates0173.C5553, NewCertificates0173.C5554, NewCertificates0173.C5555, NewCertificates0173.C5556, NewCertificates0173.C5557, NewCertificates0173.C5558, NewCertificates0173.C5559, NewCertificates0173.C5560, NewCertificates0173.C5561, NewCertificates0173.C5562, NewCertificates0173.C5563} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0173.obstruction5548
  · exact NewCertificates0173.obstruction5549
  · exact NewCertificates0173.obstruction5550
  · exact NewCertificates0173.obstruction5551
  · exact NewCertificates0173.obstruction5552
  · exact NewCertificates0173.obstruction5553
  · exact NewCertificates0173.obstruction5554
  · exact NewCertificates0173.obstruction5555
  · exact NewCertificates0173.obstruction5556
  · exact NewCertificates0173.obstruction5557
  · exact NewCertificates0173.obstruction5558
  · exact NewCertificates0173.obstruction5559
  · exact NewCertificates0173.obstruction5560
  · exact NewCertificates0173.obstruction5561
  · exact NewCertificates0173.obstruction5562
  · exact NewCertificates0173.obstruction5563
end Nut8.FiniteSupport114
