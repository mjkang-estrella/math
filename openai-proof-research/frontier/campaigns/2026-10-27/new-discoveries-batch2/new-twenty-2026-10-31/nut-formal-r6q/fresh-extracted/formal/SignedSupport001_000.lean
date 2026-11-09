import SupportData001
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport001
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0001.C32, NewCertificates0001.C33, NewCertificates0001.C34, NewCertificates0001.C35, NewCertificates0001.C36, NewCertificates0001.C37, NewCertificates0001.C38, NewCertificates0001.C39, NewCertificates0001.C40, NewCertificates0001.C41, NewCertificates0001.C42, NewCertificates0001.C43, NewCertificates0001.C44, NewCertificates0001.C45, NewCertificates0001.C46, NewCertificates0001.C47, NewCertificates0001.C48, NewCertificates0001.C49, NewCertificates0001.C50, NewCertificates0001.C51, NewCertificates0001.C52, NewCertificates0001.C53, NewCertificates0001.C54, NewCertificates0001.C55, NewCertificates0001.C56, NewCertificates0001.C57, NewCertificates0001.C58, NewCertificates0001.C59, NewCertificates0001.C60, NewCertificates0001.C61, NewCertificates0001.C62, NewCertificates0001.C63} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0002.C64, NewCertificates0002.C65, NewCertificates0002.C66, NewCertificates0002.C67, NewCertificates0002.C68, NewCertificates0002.C69, NewCertificates0002.C70, NewCertificates0002.C71, NewCertificates0002.C72, NewCertificates0002.C73, NewCertificates0002.C74, NewCertificates0002.C75, NewCertificates0002.C76, NewCertificates0002.C77, NewCertificates0002.C78, NewCertificates0002.C79} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0001.obstruction32
  · exact NewCertificates0001.obstruction33
  · exact NewCertificates0001.obstruction34
  · exact NewCertificates0001.obstruction35
  · exact NewCertificates0001.obstruction36
  · exact NewCertificates0001.obstruction37
  · exact NewCertificates0001.obstruction38
  · exact NewCertificates0001.obstruction39
  · exact NewCertificates0001.obstruction40
  · exact NewCertificates0001.obstruction41
  · exact NewCertificates0001.obstruction42
  · exact NewCertificates0001.obstruction43
  · exact NewCertificates0001.obstruction44
  · exact NewCertificates0001.obstruction45
  · exact NewCertificates0001.obstruction46
  · exact NewCertificates0001.obstruction47
  · exact NewCertificates0001.obstruction48
  · exact NewCertificates0001.obstruction49
  · exact NewCertificates0001.obstruction50
  · exact NewCertificates0001.obstruction51
  · exact NewCertificates0001.obstruction52
  · exact NewCertificates0001.obstruction53
  · exact NewCertificates0001.obstruction54
  · exact NewCertificates0001.obstruction55
  · exact NewCertificates0001.obstruction56
  · exact NewCertificates0001.obstruction57
  · exact NewCertificates0001.obstruction58
  · exact NewCertificates0001.obstruction59
  · exact NewCertificates0001.obstruction60
  · exact NewCertificates0001.obstruction61
  · exact NewCertificates0001.obstruction62
  · exact NewCertificates0001.obstruction63
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0002.obstruction64
  · exact NewCertificates0002.obstruction65
  · exact NewCertificates0002.obstruction66
  · exact NewCertificates0002.obstruction67
  · exact NewCertificates0002.obstruction68
  · exact NewCertificates0002.obstruction69
  · exact NewCertificates0002.obstruction70
  · exact NewCertificates0002.obstruction71
  · exact NewCertificates0002.obstruction72
  · exact NewCertificates0002.obstruction73
  · exact NewCertificates0002.obstruction74
  · exact NewCertificates0002.obstruction75
  · exact NewCertificates0002.obstruction76
  · exact NewCertificates0002.obstruction77
  · exact NewCertificates0002.obstruction78
  · exact NewCertificates0002.obstruction79
end Nut8.FiniteSupport001
