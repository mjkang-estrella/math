import SignedCatalogue
import NewCertificates0173
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport114
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 4, 2, 3, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0173.C5548, NewCertificates0173.C5549, NewCertificates0173.C5550, NewCertificates0173.C5551, NewCertificates0173.C5552, NewCertificates0173.C5553, NewCertificates0173.C5554, NewCertificates0173.C5555, NewCertificates0173.C5556, NewCertificates0173.C5557, NewCertificates0173.C5558, NewCertificates0173.C5559, NewCertificates0173.C5560, NewCertificates0173.C5561, NewCertificates0173.C5562, NewCertificates0173.C5563}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 509782416641016000).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 509782416641016000 D i ∧ offSum 509782416641016000 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 509782416641016000 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 509782416641016000 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 509782416641016000 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport114
