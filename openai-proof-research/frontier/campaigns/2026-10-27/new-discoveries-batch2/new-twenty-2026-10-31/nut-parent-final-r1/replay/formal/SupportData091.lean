import SignedCatalogue
import NewCertificates0131
import NewCertificates0132
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport091
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 2, 6, 1, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0131.C4206, NewCertificates0131.C4207, NewCertificates0131.C4208, NewCertificates0131.C4209, NewCertificates0131.C4210, NewCertificates0131.C4211, NewCertificates0131.C4212, NewCertificates0131.C4213, NewCertificates0131.C4214, NewCertificates0131.C4215, NewCertificates0131.C4216, NewCertificates0131.C4217, NewCertificates0131.C4218, NewCertificates0131.C4219, NewCertificates0131.C4220, NewCertificates0131.C4221, NewCertificates0131.C4222, NewCertificates0131.C4223, NewCertificates0132.C4224, NewCertificates0132.C4225, NewCertificates0132.C4226, NewCertificates0132.C4227, NewCertificates0132.C4228, NewCertificates0132.C4229, NewCertificates0132.C4230, NewCertificates0132.C4231, NewCertificates0132.C4232, NewCertificates0132.C4233, NewCertificates0132.C4234, NewCertificates0132.C4235, NewCertificates0132.C4236, NewCertificates0132.C4237}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1813354858022457472).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1813354858022457472 D i ∧ offSum 1813354858022457472 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1813354858022457472 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1813354858022457472 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1813354858022457472 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport091
