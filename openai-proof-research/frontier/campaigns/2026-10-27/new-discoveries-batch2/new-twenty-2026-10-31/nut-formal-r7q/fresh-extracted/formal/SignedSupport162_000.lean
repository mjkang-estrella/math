import SupportData162
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport162
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0238.C7620, NewCertificates0238.C7621, NewCertificates0238.C7622, NewCertificates0238.C7623, NewCertificates0238.C7624, NewCertificates0238.C7625, NewCertificates0238.C7626, NewCertificates0238.C7627, NewCertificates0238.C7628, NewCertificates0238.C7629, NewCertificates0238.C7630, NewCertificates0238.C7631, NewCertificates0238.C7632, NewCertificates0238.C7633, NewCertificates0238.C7634, NewCertificates0238.C7635, NewCertificates0238.C7636, NewCertificates0238.C7637, NewCertificates0238.C7638, NewCertificates0238.C7639, NewCertificates0238.C7640, NewCertificates0238.C7641, NewCertificates0238.C7642, NewCertificates0238.C7643, NewCertificates0238.C7644, NewCertificates0238.C7645, NewCertificates0238.C7646, NewCertificates0238.C7647, NewCertificates0239.C7648, NewCertificates0239.C7649, NewCertificates0239.C7650, NewCertificates0239.C7651} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0238.obstruction7620
  · exact NewCertificates0238.obstruction7621
  · exact NewCertificates0238.obstruction7622
  · exact NewCertificates0238.obstruction7623
  · exact NewCertificates0238.obstruction7624
  · exact NewCertificates0238.obstruction7625
  · exact NewCertificates0238.obstruction7626
  · exact NewCertificates0238.obstruction7627
  · exact NewCertificates0238.obstruction7628
  · exact NewCertificates0238.obstruction7629
  · exact NewCertificates0238.obstruction7630
  · exact NewCertificates0238.obstruction7631
  · exact NewCertificates0238.obstruction7632
  · exact NewCertificates0238.obstruction7633
  · exact NewCertificates0238.obstruction7634
  · exact NewCertificates0238.obstruction7635
  · exact NewCertificates0238.obstruction7636
  · exact NewCertificates0238.obstruction7637
  · exact NewCertificates0238.obstruction7638
  · exact NewCertificates0238.obstruction7639
  · exact NewCertificates0238.obstruction7640
  · exact NewCertificates0238.obstruction7641
  · exact NewCertificates0238.obstruction7642
  · exact NewCertificates0238.obstruction7643
  · exact NewCertificates0238.obstruction7644
  · exact NewCertificates0238.obstruction7645
  · exact NewCertificates0238.obstruction7646
  · exact NewCertificates0238.obstruction7647
  · exact NewCertificates0239.obstruction7648
  · exact NewCertificates0239.obstruction7649
  · exact NewCertificates0239.obstruction7650
  · exact NewCertificates0239.obstruction7651
end Nut8.FiniteSupport162
