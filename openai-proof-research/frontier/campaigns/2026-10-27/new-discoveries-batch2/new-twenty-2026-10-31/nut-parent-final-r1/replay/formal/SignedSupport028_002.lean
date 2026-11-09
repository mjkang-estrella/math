import SupportData028
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport028
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0044.C1408, NewCertificates0044.C1409, NewCertificates0044.C1410, NewCertificates0044.C1411, NewCertificates0044.C1412, NewCertificates0044.C1413, NewCertificates0044.C1414, NewCertificates0044.C1415} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0044.C1416, NewCertificates0044.C1417, NewCertificates0044.C1418, NewCertificates0044.C1419} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0044.obstruction1408
  · exact NewCertificates0044.obstruction1409
  · exact NewCertificates0044.obstruction1410
  · exact NewCertificates0044.obstruction1411
  · exact NewCertificates0044.obstruction1412
  · exact NewCertificates0044.obstruction1413
  · exact NewCertificates0044.obstruction1414
  · exact NewCertificates0044.obstruction1415
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0044.obstruction1416
  · exact NewCertificates0044.obstruction1417
  · exact NewCertificates0044.obstruction1418
  · exact NewCertificates0044.obstruction1419
end Nut8.FiniteSupport028
