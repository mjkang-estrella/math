import SupportData009
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport009
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0013.C432, NewCertificates0013.C433, NewCertificates0013.C434, NewCertificates0013.C435, NewCertificates0013.C436, NewCertificates0013.C437, NewCertificates0013.C438, NewCertificates0013.C439, NewCertificates0013.C440, NewCertificates0013.C441, NewCertificates0013.C442, NewCertificates0013.C443, NewCertificates0013.C444, NewCertificates0013.C445, NewCertificates0013.C446, NewCertificates0013.C447, NewCertificates0014.C448, NewCertificates0014.C449, NewCertificates0014.C450, NewCertificates0014.C451, NewCertificates0014.C452, NewCertificates0014.C453, NewCertificates0014.C454, NewCertificates0014.C455, NewCertificates0014.C456, NewCertificates0014.C457, NewCertificates0014.C458, NewCertificates0014.C459, NewCertificates0014.C460, NewCertificates0014.C461, NewCertificates0014.C462, NewCertificates0014.C463} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0014.C464, NewCertificates0014.C465, NewCertificates0014.C466, NewCertificates0014.C467, NewCertificates0014.C468, NewCertificates0014.C469, NewCertificates0014.C470, NewCertificates0014.C471, NewCertificates0014.C472, NewCertificates0014.C473, NewCertificates0014.C474, NewCertificates0014.C475, NewCertificates0014.C476, NewCertificates0014.C477, NewCertificates0014.C478, NewCertificates0014.C479} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0013.obstruction432
  · exact NewCertificates0013.obstruction433
  · exact NewCertificates0013.obstruction434
  · exact NewCertificates0013.obstruction435
  · exact NewCertificates0013.obstruction436
  · exact NewCertificates0013.obstruction437
  · exact NewCertificates0013.obstruction438
  · exact NewCertificates0013.obstruction439
  · exact NewCertificates0013.obstruction440
  · exact NewCertificates0013.obstruction441
  · exact NewCertificates0013.obstruction442
  · exact NewCertificates0013.obstruction443
  · exact NewCertificates0013.obstruction444
  · exact NewCertificates0013.obstruction445
  · exact NewCertificates0013.obstruction446
  · exact NewCertificates0013.obstruction447
  · exact NewCertificates0014.obstruction448
  · exact NewCertificates0014.obstruction449
  · exact NewCertificates0014.obstruction450
  · exact NewCertificates0014.obstruction451
  · exact NewCertificates0014.obstruction452
  · exact NewCertificates0014.obstruction453
  · exact NewCertificates0014.obstruction454
  · exact NewCertificates0014.obstruction455
  · exact NewCertificates0014.obstruction456
  · exact NewCertificates0014.obstruction457
  · exact NewCertificates0014.obstruction458
  · exact NewCertificates0014.obstruction459
  · exact NewCertificates0014.obstruction460
  · exact NewCertificates0014.obstruction461
  · exact NewCertificates0014.obstruction462
  · exact NewCertificates0014.obstruction463
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0014.obstruction464
  · exact NewCertificates0014.obstruction465
  · exact NewCertificates0014.obstruction466
  · exact NewCertificates0014.obstruction467
  · exact NewCertificates0014.obstruction468
  · exact NewCertificates0014.obstruction469
  · exact NewCertificates0014.obstruction470
  · exact NewCertificates0014.obstruction471
  · exact NewCertificates0014.obstruction472
  · exact NewCertificates0014.obstruction473
  · exact NewCertificates0014.obstruction474
  · exact NewCertificates0014.obstruction475
  · exact NewCertificates0014.obstruction476
  · exact NewCertificates0014.obstruction477
  · exact NewCertificates0014.obstruction478
  · exact NewCertificates0014.obstruction479
end Nut8.FiniteSupport009
