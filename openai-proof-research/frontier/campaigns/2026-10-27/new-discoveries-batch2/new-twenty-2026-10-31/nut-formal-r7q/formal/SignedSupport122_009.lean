import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration36 : signedPatterns (U36.submatrix e e) p = {NewCertificates0185.C5930, NewCertificates0185.C5931, NewCertificates0185.C5932, NewCertificates0185.C5933} := by
  decide +kernel
theorem signed_enumeration37 : signedPatterns (U37.submatrix e e) p = {NewCertificates0185.C5934, NewCertificates0185.C5935, NewCertificates0185.C5936, NewCertificates0185.C5937} := by
  decide +kernel
theorem signed_enumeration38 : signedPatterns (U38.submatrix e e) p = {NewCertificates0185.C5938, NewCertificates0185.C5939, NewCertificates0185.C5940, NewCertificates0185.C5941} := by
  decide +kernel
theorem signed_enumeration39 : signedPatterns (U39.submatrix e e) p = {NewCertificates0185.C5942, NewCertificates0185.C5943, NewCertificates0185.C5944, NewCertificates0185.C5945} := by
  decide +kernel
theorem checked36 : ∀ A ∈ signedPatterns (U36.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration36]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5930
  · exact NewCertificates0185.obstruction5931
  · exact NewCertificates0185.obstruction5932
  · exact NewCertificates0185.obstruction5933
theorem checked37 : ∀ A ∈ signedPatterns (U37.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration37]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5934
  · exact NewCertificates0185.obstruction5935
  · exact NewCertificates0185.obstruction5936
  · exact NewCertificates0185.obstruction5937
theorem checked38 : ∀ A ∈ signedPatterns (U38.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration38]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5938
  · exact NewCertificates0185.obstruction5939
  · exact NewCertificates0185.obstruction5940
  · exact NewCertificates0185.obstruction5941
theorem checked39 : ∀ A ∈ signedPatterns (U39.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration39]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5942
  · exact NewCertificates0185.obstruction5943
  · exact NewCertificates0185.obstruction5944
  · exact NewCertificates0185.obstruction5945
end Nut8.FiniteSupport122
