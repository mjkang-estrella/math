import SupportData112
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport112
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0171.C5472, NewCertificates0171.C5473, NewCertificates0171.C5474, NewCertificates0171.C5475, NewCertificates0171.C5476, NewCertificates0171.C5477, NewCertificates0171.C5478, NewCertificates0171.C5479} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0171.C5480, NewCertificates0171.C5481, NewCertificates0171.C5482, NewCertificates0171.C5483} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0171.C5484, NewCertificates0171.C5485, NewCertificates0171.C5486, NewCertificates0171.C5487} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0171.C5488, NewCertificates0171.C5489, NewCertificates0171.C5490, NewCertificates0171.C5491} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5472
  · exact NewCertificates0171.obstruction5473
  · exact NewCertificates0171.obstruction5474
  · exact NewCertificates0171.obstruction5475
  · exact NewCertificates0171.obstruction5476
  · exact NewCertificates0171.obstruction5477
  · exact NewCertificates0171.obstruction5478
  · exact NewCertificates0171.obstruction5479
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5480
  · exact NewCertificates0171.obstruction5481
  · exact NewCertificates0171.obstruction5482
  · exact NewCertificates0171.obstruction5483
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5484
  · exact NewCertificates0171.obstruction5485
  · exact NewCertificates0171.obstruction5486
  · exact NewCertificates0171.obstruction5487
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0171.obstruction5488
  · exact NewCertificates0171.obstruction5489
  · exact NewCertificates0171.obstruction5490
  · exact NewCertificates0171.obstruction5491
end Nut8.FiniteSupport112
