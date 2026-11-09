import SupportData107
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport107
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0156.C4998, NewCertificates0156.C4999, NewCertificates0156.C5000, NewCertificates0156.C5001, NewCertificates0156.C5002, NewCertificates0156.C5003, NewCertificates0156.C5004, NewCertificates0156.C5005, NewCertificates0156.C5006, NewCertificates0156.C5007, NewCertificates0156.C5008, NewCertificates0156.C5009, NewCertificates0156.C5010, NewCertificates0156.C5011, NewCertificates0156.C5012, NewCertificates0156.C5013, NewCertificates0156.C5014, NewCertificates0156.C5015, NewCertificates0156.C5016, NewCertificates0156.C5017, NewCertificates0156.C5018, NewCertificates0156.C5019, NewCertificates0156.C5020, NewCertificates0156.C5021, NewCertificates0156.C5022, NewCertificates0156.C5023, NewCertificates0157.C5024, NewCertificates0157.C5025, NewCertificates0157.C5026, NewCertificates0157.C5027, NewCertificates0157.C5028, NewCertificates0157.C5029} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0156.obstruction4998
  · exact NewCertificates0156.obstruction4999
  · exact NewCertificates0156.obstruction5000
  · exact NewCertificates0156.obstruction5001
  · exact NewCertificates0156.obstruction5002
  · exact NewCertificates0156.obstruction5003
  · exact NewCertificates0156.obstruction5004
  · exact NewCertificates0156.obstruction5005
  · exact NewCertificates0156.obstruction5006
  · exact NewCertificates0156.obstruction5007
  · exact NewCertificates0156.obstruction5008
  · exact NewCertificates0156.obstruction5009
  · exact NewCertificates0156.obstruction5010
  · exact NewCertificates0156.obstruction5011
  · exact NewCertificates0156.obstruction5012
  · exact NewCertificates0156.obstruction5013
  · exact NewCertificates0156.obstruction5014
  · exact NewCertificates0156.obstruction5015
  · exact NewCertificates0156.obstruction5016
  · exact NewCertificates0156.obstruction5017
  · exact NewCertificates0156.obstruction5018
  · exact NewCertificates0156.obstruction5019
  · exact NewCertificates0156.obstruction5020
  · exact NewCertificates0156.obstruction5021
  · exact NewCertificates0156.obstruction5022
  · exact NewCertificates0156.obstruction5023
  · exact NewCertificates0157.obstruction5024
  · exact NewCertificates0157.obstruction5025
  · exact NewCertificates0157.obstruction5026
  · exact NewCertificates0157.obstruction5027
  · exact NewCertificates0157.obstruction5028
  · exact NewCertificates0157.obstruction5029
end Nut8.FiniteSupport107
