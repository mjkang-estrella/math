import SupportData017
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport017
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0025.C824, NewCertificates0025.C825, NewCertificates0025.C826, NewCertificates0025.C827, NewCertificates0025.C828, NewCertificates0025.C829, NewCertificates0025.C830, NewCertificates0025.C831, NewCertificates0026.C832, NewCertificates0026.C833, NewCertificates0026.C834, NewCertificates0026.C835, NewCertificates0026.C836, NewCertificates0026.C837, NewCertificates0026.C838, NewCertificates0026.C839, NewCertificates0026.C840, NewCertificates0026.C841, NewCertificates0026.C842, NewCertificates0026.C843, NewCertificates0026.C844, NewCertificates0026.C845, NewCertificates0026.C846, NewCertificates0026.C847, NewCertificates0026.C848, NewCertificates0026.C849, NewCertificates0026.C850, NewCertificates0026.C851, NewCertificates0026.C852, NewCertificates0026.C853, NewCertificates0026.C854, NewCertificates0026.C855} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0025.obstruction824
  · exact NewCertificates0025.obstruction825
  · exact NewCertificates0025.obstruction826
  · exact NewCertificates0025.obstruction827
  · exact NewCertificates0025.obstruction828
  · exact NewCertificates0025.obstruction829
  · exact NewCertificates0025.obstruction830
  · exact NewCertificates0025.obstruction831
  · exact NewCertificates0026.obstruction832
  · exact NewCertificates0026.obstruction833
  · exact NewCertificates0026.obstruction834
  · exact NewCertificates0026.obstruction835
  · exact NewCertificates0026.obstruction836
  · exact NewCertificates0026.obstruction837
  · exact NewCertificates0026.obstruction838
  · exact NewCertificates0026.obstruction839
  · exact NewCertificates0026.obstruction840
  · exact NewCertificates0026.obstruction841
  · exact NewCertificates0026.obstruction842
  · exact NewCertificates0026.obstruction843
  · exact NewCertificates0026.obstruction844
  · exact NewCertificates0026.obstruction845
  · exact NewCertificates0026.obstruction846
  · exact NewCertificates0026.obstruction847
  · exact NewCertificates0026.obstruction848
  · exact NewCertificates0026.obstruction849
  · exact NewCertificates0026.obstruction850
  · exact NewCertificates0026.obstruction851
  · exact NewCertificates0026.obstruction852
  · exact NewCertificates0026.obstruction853
  · exact NewCertificates0026.obstruction854
  · exact NewCertificates0026.obstruction855
end Nut8.FiniteSupport017
