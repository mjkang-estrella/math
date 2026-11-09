import SignedCatalogue
import NewCertificates0026
import NewCertificates0027
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport018
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 5, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0026.C856, NewCertificates0026.C857, NewCertificates0026.C858, NewCertificates0026.C859, NewCertificates0026.C860, NewCertificates0026.C861, NewCertificates0026.C862, NewCertificates0026.C863, NewCertificates0027.C864, NewCertificates0027.C865, NewCertificates0027.C866, NewCertificates0027.C867, NewCertificates0027.C868, NewCertificates0027.C869, NewCertificates0027.C870, NewCertificates0027.C871, NewCertificates0027.C872, NewCertificates0027.C873, NewCertificates0027.C874, NewCertificates0027.C875, NewCertificates0027.C876, NewCertificates0027.C877, NewCertificates0027.C878, NewCertificates0027.C879, NewCertificates0027.C880, NewCertificates0027.C881, NewCertificates0027.C882, NewCertificates0027.C883, NewCertificates0027.C884, NewCertificates0027.C885, NewCertificates0027.C886, NewCertificates0027.C887}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 512315692509331584).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 512315692509331584 D i ∧ offSum 512315692509331584 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 512315692509331584 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 512315692509331584 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 512315692509331584 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport018
