import SupportData018
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport018
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0026.C856, NewCertificates0026.C857, NewCertificates0026.C858, NewCertificates0026.C859, NewCertificates0026.C860, NewCertificates0026.C861, NewCertificates0026.C862, NewCertificates0026.C863, NewCertificates0027.C864, NewCertificates0027.C865, NewCertificates0027.C866, NewCertificates0027.C867, NewCertificates0027.C868, NewCertificates0027.C869, NewCertificates0027.C870, NewCertificates0027.C871, NewCertificates0027.C872, NewCertificates0027.C873, NewCertificates0027.C874, NewCertificates0027.C875, NewCertificates0027.C876, NewCertificates0027.C877, NewCertificates0027.C878, NewCertificates0027.C879, NewCertificates0027.C880, NewCertificates0027.C881, NewCertificates0027.C882, NewCertificates0027.C883, NewCertificates0027.C884, NewCertificates0027.C885, NewCertificates0027.C886, NewCertificates0027.C887} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0026.obstruction856
  · exact NewCertificates0026.obstruction857
  · exact NewCertificates0026.obstruction858
  · exact NewCertificates0026.obstruction859
  · exact NewCertificates0026.obstruction860
  · exact NewCertificates0026.obstruction861
  · exact NewCertificates0026.obstruction862
  · exact NewCertificates0026.obstruction863
  · exact NewCertificates0027.obstruction864
  · exact NewCertificates0027.obstruction865
  · exact NewCertificates0027.obstruction866
  · exact NewCertificates0027.obstruction867
  · exact NewCertificates0027.obstruction868
  · exact NewCertificates0027.obstruction869
  · exact NewCertificates0027.obstruction870
  · exact NewCertificates0027.obstruction871
  · exact NewCertificates0027.obstruction872
  · exact NewCertificates0027.obstruction873
  · exact NewCertificates0027.obstruction874
  · exact NewCertificates0027.obstruction875
  · exact NewCertificates0027.obstruction876
  · exact NewCertificates0027.obstruction877
  · exact NewCertificates0027.obstruction878
  · exact NewCertificates0027.obstruction879
  · exact NewCertificates0027.obstruction880
  · exact NewCertificates0027.obstruction881
  · exact NewCertificates0027.obstruction882
  · exact NewCertificates0027.obstruction883
  · exact NewCertificates0027.obstruction884
  · exact NewCertificates0027.obstruction885
  · exact NewCertificates0027.obstruction886
  · exact NewCertificates0027.obstruction887
end Nut8.FiniteSupport018
