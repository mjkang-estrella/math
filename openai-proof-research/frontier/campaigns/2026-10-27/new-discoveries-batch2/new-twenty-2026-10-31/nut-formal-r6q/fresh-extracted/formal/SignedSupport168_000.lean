import SupportData168
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport168
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0243.C7804, NewCertificates0243.C7805, NewCertificates0243.C7806, NewCertificates0243.C7807, NewCertificates0244.C7808, NewCertificates0244.C7809, NewCertificates0244.C7810, NewCertificates0244.C7811, NewCertificates0244.C7812, NewCertificates0244.C7813, NewCertificates0244.C7814, NewCertificates0244.C7815, NewCertificates0244.C7816, NewCertificates0244.C7817, NewCertificates0244.C7818, NewCertificates0244.C7819} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0244.C7820, NewCertificates0244.C7821, NewCertificates0244.C7822, NewCertificates0244.C7823, NewCertificates0244.C7824, NewCertificates0244.C7825, NewCertificates0244.C7826, NewCertificates0244.C7827, NewCertificates0244.C7828, NewCertificates0244.C7829, NewCertificates0244.C7830, NewCertificates0244.C7831, NewCertificates0244.C7832, NewCertificates0244.C7833, NewCertificates0244.C7834, NewCertificates0244.C7835} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0244.C7836, NewCertificates0244.C7837, NewCertificates0244.C7838, NewCertificates0244.C7839, NewCertificates0245.C7840, NewCertificates0245.C7841, NewCertificates0245.C7842, NewCertificates0245.C7843} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0243.obstruction7804
  · exact NewCertificates0243.obstruction7805
  · exact NewCertificates0243.obstruction7806
  · exact NewCertificates0243.obstruction7807
  · exact NewCertificates0244.obstruction7808
  · exact NewCertificates0244.obstruction7809
  · exact NewCertificates0244.obstruction7810
  · exact NewCertificates0244.obstruction7811
  · exact NewCertificates0244.obstruction7812
  · exact NewCertificates0244.obstruction7813
  · exact NewCertificates0244.obstruction7814
  · exact NewCertificates0244.obstruction7815
  · exact NewCertificates0244.obstruction7816
  · exact NewCertificates0244.obstruction7817
  · exact NewCertificates0244.obstruction7818
  · exact NewCertificates0244.obstruction7819
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0244.obstruction7820
  · exact NewCertificates0244.obstruction7821
  · exact NewCertificates0244.obstruction7822
  · exact NewCertificates0244.obstruction7823
  · exact NewCertificates0244.obstruction7824
  · exact NewCertificates0244.obstruction7825
  · exact NewCertificates0244.obstruction7826
  · exact NewCertificates0244.obstruction7827
  · exact NewCertificates0244.obstruction7828
  · exact NewCertificates0244.obstruction7829
  · exact NewCertificates0244.obstruction7830
  · exact NewCertificates0244.obstruction7831
  · exact NewCertificates0244.obstruction7832
  · exact NewCertificates0244.obstruction7833
  · exact NewCertificates0244.obstruction7834
  · exact NewCertificates0244.obstruction7835
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0244.obstruction7836
  · exact NewCertificates0244.obstruction7837
  · exact NewCertificates0244.obstruction7838
  · exact NewCertificates0244.obstruction7839
  · exact NewCertificates0245.obstruction7840
  · exact NewCertificates0245.obstruction7841
  · exact NewCertificates0245.obstruction7842
  · exact NewCertificates0245.obstruction7843
end Nut8.FiniteSupport168
