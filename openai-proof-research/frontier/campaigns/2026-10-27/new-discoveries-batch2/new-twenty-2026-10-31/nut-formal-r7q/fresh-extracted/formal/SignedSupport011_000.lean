import SupportData011
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport011
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0016.C512, NewCertificates0016.C513, NewCertificates0016.C514, NewCertificates0016.C515, NewCertificates0016.C516, NewCertificates0016.C517, NewCertificates0016.C518, NewCertificates0016.C519, NewCertificates0016.C520, NewCertificates0016.C521, NewCertificates0016.C522, NewCertificates0016.C523, NewCertificates0016.C524, NewCertificates0016.C525, NewCertificates0016.C526, NewCertificates0016.C527} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0016.C528, NewCertificates0016.C529, NewCertificates0016.C530, NewCertificates0016.C531, NewCertificates0016.C532, NewCertificates0016.C533, NewCertificates0016.C534, NewCertificates0016.C535, NewCertificates0016.C536, NewCertificates0016.C537, NewCertificates0016.C538, NewCertificates0016.C539, NewCertificates0016.C540, NewCertificates0016.C541, NewCertificates0016.C542, NewCertificates0016.C543} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0017.C544, NewCertificates0017.C545, NewCertificates0017.C546, NewCertificates0017.C547, NewCertificates0017.C548, NewCertificates0017.C549, NewCertificates0017.C550, NewCertificates0017.C551, NewCertificates0017.C552, NewCertificates0017.C553, NewCertificates0017.C554, NewCertificates0017.C555, NewCertificates0017.C556, NewCertificates0017.C557, NewCertificates0017.C558, NewCertificates0017.C559} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0016.obstruction512
  · exact NewCertificates0016.obstruction513
  · exact NewCertificates0016.obstruction514
  · exact NewCertificates0016.obstruction515
  · exact NewCertificates0016.obstruction516
  · exact NewCertificates0016.obstruction517
  · exact NewCertificates0016.obstruction518
  · exact NewCertificates0016.obstruction519
  · exact NewCertificates0016.obstruction520
  · exact NewCertificates0016.obstruction521
  · exact NewCertificates0016.obstruction522
  · exact NewCertificates0016.obstruction523
  · exact NewCertificates0016.obstruction524
  · exact NewCertificates0016.obstruction525
  · exact NewCertificates0016.obstruction526
  · exact NewCertificates0016.obstruction527
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0016.obstruction528
  · exact NewCertificates0016.obstruction529
  · exact NewCertificates0016.obstruction530
  · exact NewCertificates0016.obstruction531
  · exact NewCertificates0016.obstruction532
  · exact NewCertificates0016.obstruction533
  · exact NewCertificates0016.obstruction534
  · exact NewCertificates0016.obstruction535
  · exact NewCertificates0016.obstruction536
  · exact NewCertificates0016.obstruction537
  · exact NewCertificates0016.obstruction538
  · exact NewCertificates0016.obstruction539
  · exact NewCertificates0016.obstruction540
  · exact NewCertificates0016.obstruction541
  · exact NewCertificates0016.obstruction542
  · exact NewCertificates0016.obstruction543
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0017.obstruction544
  · exact NewCertificates0017.obstruction545
  · exact NewCertificates0017.obstruction546
  · exact NewCertificates0017.obstruction547
  · exact NewCertificates0017.obstruction548
  · exact NewCertificates0017.obstruction549
  · exact NewCertificates0017.obstruction550
  · exact NewCertificates0017.obstruction551
  · exact NewCertificates0017.obstruction552
  · exact NewCertificates0017.obstruction553
  · exact NewCertificates0017.obstruction554
  · exact NewCertificates0017.obstruction555
  · exact NewCertificates0017.obstruction556
  · exact NewCertificates0017.obstruction557
  · exact NewCertificates0017.obstruction558
  · exact NewCertificates0017.obstruction559
end Nut8.FiniteSupport011
