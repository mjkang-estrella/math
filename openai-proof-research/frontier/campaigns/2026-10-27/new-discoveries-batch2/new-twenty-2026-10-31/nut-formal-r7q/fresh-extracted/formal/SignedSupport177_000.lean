import SupportData177
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport177
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0257.C8236, NewCertificates0257.C8237, NewCertificates0257.C8238, NewCertificates0257.C8239, NewCertificates0257.C8240, NewCertificates0257.C8241, NewCertificates0257.C8242, NewCertificates0257.C8243, NewCertificates0257.C8244, NewCertificates0257.C8245, NewCertificates0257.C8246, NewCertificates0257.C8247, NewCertificates0257.C8248, NewCertificates0257.C8249, NewCertificates0257.C8250, NewCertificates0257.C8251} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0257.C8252, NewCertificates0257.C8253, NewCertificates0257.C8254, NewCertificates0257.C8255, NewCertificates0258.C8256, NewCertificates0258.C8257, NewCertificates0258.C8258, NewCertificates0258.C8259, NewCertificates0258.C8260, NewCertificates0258.C8261, NewCertificates0258.C8262, NewCertificates0258.C8263, NewCertificates0258.C8264, NewCertificates0258.C8265, NewCertificates0258.C8266, NewCertificates0258.C8267} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0258.C8268, NewCertificates0258.C8269, NewCertificates0258.C8270, NewCertificates0258.C8271, NewCertificates0258.C8272, NewCertificates0258.C8273, NewCertificates0258.C8274, NewCertificates0258.C8275, NewCertificates0258.C8276, NewCertificates0258.C8277, NewCertificates0258.C8278, NewCertificates0258.C8279, NewCertificates0258.C8280, NewCertificates0258.C8281, NewCertificates0258.C8282, NewCertificates0258.C8283} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0258.C8284, NewCertificates0258.C8285, NewCertificates0258.C8286, NewCertificates0258.C8287, NewCertificates0259.C8288, NewCertificates0259.C8289, NewCertificates0259.C8290, NewCertificates0259.C8291} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0257.obstruction8236
  · exact NewCertificates0257.obstruction8237
  · exact NewCertificates0257.obstruction8238
  · exact NewCertificates0257.obstruction8239
  · exact NewCertificates0257.obstruction8240
  · exact NewCertificates0257.obstruction8241
  · exact NewCertificates0257.obstruction8242
  · exact NewCertificates0257.obstruction8243
  · exact NewCertificates0257.obstruction8244
  · exact NewCertificates0257.obstruction8245
  · exact NewCertificates0257.obstruction8246
  · exact NewCertificates0257.obstruction8247
  · exact NewCertificates0257.obstruction8248
  · exact NewCertificates0257.obstruction8249
  · exact NewCertificates0257.obstruction8250
  · exact NewCertificates0257.obstruction8251
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0257.obstruction8252
  · exact NewCertificates0257.obstruction8253
  · exact NewCertificates0257.obstruction8254
  · exact NewCertificates0257.obstruction8255
  · exact NewCertificates0258.obstruction8256
  · exact NewCertificates0258.obstruction8257
  · exact NewCertificates0258.obstruction8258
  · exact NewCertificates0258.obstruction8259
  · exact NewCertificates0258.obstruction8260
  · exact NewCertificates0258.obstruction8261
  · exact NewCertificates0258.obstruction8262
  · exact NewCertificates0258.obstruction8263
  · exact NewCertificates0258.obstruction8264
  · exact NewCertificates0258.obstruction8265
  · exact NewCertificates0258.obstruction8266
  · exact NewCertificates0258.obstruction8267
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0258.obstruction8268
  · exact NewCertificates0258.obstruction8269
  · exact NewCertificates0258.obstruction8270
  · exact NewCertificates0258.obstruction8271
  · exact NewCertificates0258.obstruction8272
  · exact NewCertificates0258.obstruction8273
  · exact NewCertificates0258.obstruction8274
  · exact NewCertificates0258.obstruction8275
  · exact NewCertificates0258.obstruction8276
  · exact NewCertificates0258.obstruction8277
  · exact NewCertificates0258.obstruction8278
  · exact NewCertificates0258.obstruction8279
  · exact NewCertificates0258.obstruction8280
  · exact NewCertificates0258.obstruction8281
  · exact NewCertificates0258.obstruction8282
  · exact NewCertificates0258.obstruction8283
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0258.obstruction8284
  · exact NewCertificates0258.obstruction8285
  · exact NewCertificates0258.obstruction8286
  · exact NewCertificates0258.obstruction8287
  · exact NewCertificates0259.obstruction8288
  · exact NewCertificates0259.obstruction8289
  · exact NewCertificates0259.obstruction8290
  · exact NewCertificates0259.obstruction8291
end Nut8.FiniteSupport177
