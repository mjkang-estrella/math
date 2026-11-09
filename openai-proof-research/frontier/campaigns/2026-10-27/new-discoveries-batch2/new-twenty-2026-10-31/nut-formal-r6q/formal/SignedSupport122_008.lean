import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration32 : signedPatterns (U32.submatrix e e) p = {NewCertificates0184.C5916, NewCertificates0184.C5917, NewCertificates0184.C5918, NewCertificates0184.C5919} := by
  decide +kernel
theorem signed_enumeration33 : signedPatterns (U33.submatrix e e) p = {NewCertificates0185.C5920, NewCertificates0185.C5921} := by
  decide +kernel
theorem signed_enumeration34 : signedPatterns (U34.submatrix e e) p = {NewCertificates0185.C5922, NewCertificates0185.C5923, NewCertificates0185.C5924, NewCertificates0185.C5925} := by
  decide +kernel
theorem signed_enumeration35 : signedPatterns (U35.submatrix e e) p = {NewCertificates0185.C5926, NewCertificates0185.C5927, NewCertificates0185.C5928, NewCertificates0185.C5929} := by
  decide +kernel
theorem checked32 : ∀ A ∈ signedPatterns (U32.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration32]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5916
  · exact NewCertificates0184.obstruction5917
  · exact NewCertificates0184.obstruction5918
  · exact NewCertificates0184.obstruction5919
theorem checked33 : ∀ A ∈ signedPatterns (U33.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration33]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0185.obstruction5920
  · exact NewCertificates0185.obstruction5921
theorem checked34 : ∀ A ∈ signedPatterns (U34.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration34]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5922
  · exact NewCertificates0185.obstruction5923
  · exact NewCertificates0185.obstruction5924
  · exact NewCertificates0185.obstruction5925
theorem checked35 : ∀ A ∈ signedPatterns (U35.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration35]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5926
  · exact NewCertificates0185.obstruction5927
  · exact NewCertificates0185.obstruction5928
  · exact NewCertificates0185.obstruction5929
end Nut8.FiniteSupport122
