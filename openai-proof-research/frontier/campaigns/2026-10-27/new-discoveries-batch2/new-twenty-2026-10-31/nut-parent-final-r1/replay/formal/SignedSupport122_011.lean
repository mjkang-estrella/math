import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration44 : signedPatterns (U44.submatrix e e) p = {NewCertificates0186.C5962, NewCertificates0186.C5963, NewCertificates0186.C5964, NewCertificates0186.C5965} := by
  decide +kernel
theorem signed_enumeration45 : signedPatterns (U45.submatrix e e) p = {NewCertificates0186.C5966, NewCertificates0186.C5967, NewCertificates0186.C5968, NewCertificates0186.C5969} := by
  decide +kernel
theorem signed_enumeration46 : signedPatterns (U46.submatrix e e) p = {NewCertificates0186.C5970, NewCertificates0186.C5971} := by
  decide +kernel
theorem checked44 : ∀ A ∈ signedPatterns (U44.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration44]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5962
  · exact NewCertificates0186.obstruction5963
  · exact NewCertificates0186.obstruction5964
  · exact NewCertificates0186.obstruction5965
theorem checked45 : ∀ A ∈ signedPatterns (U45.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration45]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5966
  · exact NewCertificates0186.obstruction5967
  · exact NewCertificates0186.obstruction5968
  · exact NewCertificates0186.obstruction5969
theorem checked46 : ∀ A ∈ signedPatterns (U46.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration46]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0186.obstruction5970
  · exact NewCertificates0186.obstruction5971
end Nut8.FiniteSupport122
