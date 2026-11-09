import SupportData005
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport005
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0008.C280, NewCertificates0008.C281, NewCertificates0008.C282, NewCertificates0008.C283, NewCertificates0008.C284, NewCertificates0008.C285, NewCertificates0008.C286, NewCertificates0008.C287} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0009.C288, NewCertificates0009.C289, NewCertificates0009.C290, NewCertificates0009.C291, NewCertificates0009.C292, NewCertificates0009.C293, NewCertificates0009.C294, NewCertificates0009.C295, NewCertificates0009.C296, NewCertificates0009.C297, NewCertificates0009.C298, NewCertificates0009.C299, NewCertificates0009.C300, NewCertificates0009.C301, NewCertificates0009.C302, NewCertificates0009.C303} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0009.C304, NewCertificates0009.C305, NewCertificates0009.C306, NewCertificates0009.C307, NewCertificates0009.C308, NewCertificates0009.C309, NewCertificates0009.C310, NewCertificates0009.C311} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0009.C312, NewCertificates0009.C313, NewCertificates0009.C314, NewCertificates0009.C315, NewCertificates0009.C316, NewCertificates0009.C317, NewCertificates0009.C318, NewCertificates0009.C319} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0008.obstruction280
  · exact NewCertificates0008.obstruction281
  · exact NewCertificates0008.obstruction282
  · exact NewCertificates0008.obstruction283
  · exact NewCertificates0008.obstruction284
  · exact NewCertificates0008.obstruction285
  · exact NewCertificates0008.obstruction286
  · exact NewCertificates0008.obstruction287
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0009.obstruction288
  · exact NewCertificates0009.obstruction289
  · exact NewCertificates0009.obstruction290
  · exact NewCertificates0009.obstruction291
  · exact NewCertificates0009.obstruction292
  · exact NewCertificates0009.obstruction293
  · exact NewCertificates0009.obstruction294
  · exact NewCertificates0009.obstruction295
  · exact NewCertificates0009.obstruction296
  · exact NewCertificates0009.obstruction297
  · exact NewCertificates0009.obstruction298
  · exact NewCertificates0009.obstruction299
  · exact NewCertificates0009.obstruction300
  · exact NewCertificates0009.obstruction301
  · exact NewCertificates0009.obstruction302
  · exact NewCertificates0009.obstruction303
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0009.obstruction304
  · exact NewCertificates0009.obstruction305
  · exact NewCertificates0009.obstruction306
  · exact NewCertificates0009.obstruction307
  · exact NewCertificates0009.obstruction308
  · exact NewCertificates0009.obstruction309
  · exact NewCertificates0009.obstruction310
  · exact NewCertificates0009.obstruction311
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0009.obstruction312
  · exact NewCertificates0009.obstruction313
  · exact NewCertificates0009.obstruction314
  · exact NewCertificates0009.obstruction315
  · exact NewCertificates0009.obstruction316
  · exact NewCertificates0009.obstruction317
  · exact NewCertificates0009.obstruction318
  · exact NewCertificates0009.obstruction319
end Nut8.FiniteSupport005
