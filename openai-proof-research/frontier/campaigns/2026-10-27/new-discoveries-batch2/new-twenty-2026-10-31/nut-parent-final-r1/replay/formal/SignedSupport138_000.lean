import SupportData138
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport138
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0201.C6452, NewCertificates0201.C6453, NewCertificates0201.C6454, NewCertificates0201.C6455, NewCertificates0201.C6456, NewCertificates0201.C6457, NewCertificates0201.C6458, NewCertificates0201.C6459, NewCertificates0201.C6460, NewCertificates0201.C6461, NewCertificates0201.C6462, NewCertificates0201.C6463, NewCertificates0202.C6464, NewCertificates0202.C6465, NewCertificates0202.C6466, NewCertificates0202.C6467, NewCertificates0202.C6468, NewCertificates0202.C6469, NewCertificates0202.C6470, NewCertificates0202.C6471, NewCertificates0202.C6472, NewCertificates0202.C6473, NewCertificates0202.C6474, NewCertificates0202.C6475, NewCertificates0202.C6476, NewCertificates0202.C6477, NewCertificates0202.C6478, NewCertificates0202.C6479, NewCertificates0202.C6480, NewCertificates0202.C6481, NewCertificates0202.C6482, NewCertificates0202.C6483} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0201.obstruction6452
  · exact NewCertificates0201.obstruction6453
  · exact NewCertificates0201.obstruction6454
  · exact NewCertificates0201.obstruction6455
  · exact NewCertificates0201.obstruction6456
  · exact NewCertificates0201.obstruction6457
  · exact NewCertificates0201.obstruction6458
  · exact NewCertificates0201.obstruction6459
  · exact NewCertificates0201.obstruction6460
  · exact NewCertificates0201.obstruction6461
  · exact NewCertificates0201.obstruction6462
  · exact NewCertificates0201.obstruction6463
  · exact NewCertificates0202.obstruction6464
  · exact NewCertificates0202.obstruction6465
  · exact NewCertificates0202.obstruction6466
  · exact NewCertificates0202.obstruction6467
  · exact NewCertificates0202.obstruction6468
  · exact NewCertificates0202.obstruction6469
  · exact NewCertificates0202.obstruction6470
  · exact NewCertificates0202.obstruction6471
  · exact NewCertificates0202.obstruction6472
  · exact NewCertificates0202.obstruction6473
  · exact NewCertificates0202.obstruction6474
  · exact NewCertificates0202.obstruction6475
  · exact NewCertificates0202.obstruction6476
  · exact NewCertificates0202.obstruction6477
  · exact NewCertificates0202.obstruction6478
  · exact NewCertificates0202.obstruction6479
  · exact NewCertificates0202.obstruction6480
  · exact NewCertificates0202.obstruction6481
  · exact NewCertificates0202.obstruction6482
  · exact NewCertificates0202.obstruction6483
end Nut8.FiniteSupport138
