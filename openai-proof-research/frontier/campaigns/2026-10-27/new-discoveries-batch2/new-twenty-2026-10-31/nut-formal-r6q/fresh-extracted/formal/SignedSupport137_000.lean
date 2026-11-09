import SupportData137
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport137
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0200.C6420, NewCertificates0200.C6421, NewCertificates0200.C6422, NewCertificates0200.C6423, NewCertificates0200.C6424, NewCertificates0200.C6425, NewCertificates0200.C6426, NewCertificates0200.C6427, NewCertificates0200.C6428, NewCertificates0200.C6429, NewCertificates0200.C6430, NewCertificates0200.C6431, NewCertificates0201.C6432, NewCertificates0201.C6433, NewCertificates0201.C6434, NewCertificates0201.C6435, NewCertificates0201.C6436, NewCertificates0201.C6437, NewCertificates0201.C6438, NewCertificates0201.C6439, NewCertificates0201.C6440, NewCertificates0201.C6441, NewCertificates0201.C6442, NewCertificates0201.C6443, NewCertificates0201.C6444, NewCertificates0201.C6445, NewCertificates0201.C6446, NewCertificates0201.C6447, NewCertificates0201.C6448, NewCertificates0201.C6449, NewCertificates0201.C6450, NewCertificates0201.C6451} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0200.obstruction6420
  · exact NewCertificates0200.obstruction6421
  · exact NewCertificates0200.obstruction6422
  · exact NewCertificates0200.obstruction6423
  · exact NewCertificates0200.obstruction6424
  · exact NewCertificates0200.obstruction6425
  · exact NewCertificates0200.obstruction6426
  · exact NewCertificates0200.obstruction6427
  · exact NewCertificates0200.obstruction6428
  · exact NewCertificates0200.obstruction6429
  · exact NewCertificates0200.obstruction6430
  · exact NewCertificates0200.obstruction6431
  · exact NewCertificates0201.obstruction6432
  · exact NewCertificates0201.obstruction6433
  · exact NewCertificates0201.obstruction6434
  · exact NewCertificates0201.obstruction6435
  · exact NewCertificates0201.obstruction6436
  · exact NewCertificates0201.obstruction6437
  · exact NewCertificates0201.obstruction6438
  · exact NewCertificates0201.obstruction6439
  · exact NewCertificates0201.obstruction6440
  · exact NewCertificates0201.obstruction6441
  · exact NewCertificates0201.obstruction6442
  · exact NewCertificates0201.obstruction6443
  · exact NewCertificates0201.obstruction6444
  · exact NewCertificates0201.obstruction6445
  · exact NewCertificates0201.obstruction6446
  · exact NewCertificates0201.obstruction6447
  · exact NewCertificates0201.obstruction6448
  · exact NewCertificates0201.obstruction6449
  · exact NewCertificates0201.obstruction6450
  · exact NewCertificates0201.obstruction6451
end Nut8.FiniteSupport137
