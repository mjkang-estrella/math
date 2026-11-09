import SupportData111
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport111
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0166.C5312, NewCertificates0166.C5313, NewCertificates0166.C5314, NewCertificates0166.C5315, NewCertificates0166.C5316, NewCertificates0166.C5317, NewCertificates0166.C5318, NewCertificates0166.C5319} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0166.C5320, NewCertificates0166.C5321, NewCertificates0166.C5322, NewCertificates0166.C5323, NewCertificates0166.C5324, NewCertificates0166.C5325, NewCertificates0166.C5326, NewCertificates0166.C5327} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0166.C5328, NewCertificates0166.C5329, NewCertificates0166.C5330, NewCertificates0166.C5331, NewCertificates0166.C5332, NewCertificates0166.C5333, NewCertificates0166.C5334, NewCertificates0166.C5335} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0166.C5336, NewCertificates0166.C5337, NewCertificates0166.C5338, NewCertificates0166.C5339, NewCertificates0166.C5340, NewCertificates0166.C5341, NewCertificates0166.C5342, NewCertificates0166.C5343} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0166.obstruction5312
  · exact NewCertificates0166.obstruction5313
  · exact NewCertificates0166.obstruction5314
  · exact NewCertificates0166.obstruction5315
  · exact NewCertificates0166.obstruction5316
  · exact NewCertificates0166.obstruction5317
  · exact NewCertificates0166.obstruction5318
  · exact NewCertificates0166.obstruction5319
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0166.obstruction5320
  · exact NewCertificates0166.obstruction5321
  · exact NewCertificates0166.obstruction5322
  · exact NewCertificates0166.obstruction5323
  · exact NewCertificates0166.obstruction5324
  · exact NewCertificates0166.obstruction5325
  · exact NewCertificates0166.obstruction5326
  · exact NewCertificates0166.obstruction5327
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0166.obstruction5328
  · exact NewCertificates0166.obstruction5329
  · exact NewCertificates0166.obstruction5330
  · exact NewCertificates0166.obstruction5331
  · exact NewCertificates0166.obstruction5332
  · exact NewCertificates0166.obstruction5333
  · exact NewCertificates0166.obstruction5334
  · exact NewCertificates0166.obstruction5335
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0166.obstruction5336
  · exact NewCertificates0166.obstruction5337
  · exact NewCertificates0166.obstruction5338
  · exact NewCertificates0166.obstruction5339
  · exact NewCertificates0166.obstruction5340
  · exact NewCertificates0166.obstruction5341
  · exact NewCertificates0166.obstruction5342
  · exact NewCertificates0166.obstruction5343
end Nut8.FiniteSupport111
