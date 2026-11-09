import SignedCatalogue
import NewCertificates0126
import NewCertificates0127
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport088
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 3, 5, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0126.C4062, NewCertificates0126.C4063, NewCertificates0127.C4064, NewCertificates0127.C4065, NewCertificates0127.C4066, NewCertificates0127.C4067, NewCertificates0127.C4068, NewCertificates0127.C4069, NewCertificates0127.C4070, NewCertificates0127.C4071, NewCertificates0127.C4072, NewCertificates0127.C4073, NewCertificates0127.C4074, NewCertificates0127.C4075, NewCertificates0127.C4076, NewCertificates0127.C4077, NewCertificates0127.C4078, NewCertificates0127.C4079, NewCertificates0127.C4080, NewCertificates0127.C4081, NewCertificates0127.C4082, NewCertificates0127.C4083, NewCertificates0127.C4084, NewCertificates0127.C4085, NewCertificates0127.C4086, NewCertificates0127.C4087, NewCertificates0127.C4088, NewCertificates0127.C4089, NewCertificates0127.C4090, NewCertificates0127.C4091, NewCertificates0127.C4092, NewCertificates0127.C4093}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1381563343170474112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1381563343170474112 D i ∧ offSum 1381563343170474112 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1381563343170474112 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1381563343170474112 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1381563343170474112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport088
