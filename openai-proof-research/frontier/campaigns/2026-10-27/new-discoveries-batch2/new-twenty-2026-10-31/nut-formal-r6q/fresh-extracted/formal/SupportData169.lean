import SignedCatalogue
import NewCertificates0245
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport169
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 7, 1, 2, 6, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0245.C7844, NewCertificates0245.C7845, NewCertificates0245.C7846, NewCertificates0245.C7847, NewCertificates0245.C7848, NewCertificates0245.C7849, NewCertificates0245.C7850, NewCertificates0245.C7851, NewCertificates0245.C7852, NewCertificates0245.C7853, NewCertificates0245.C7854, NewCertificates0245.C7855, NewCertificates0245.C7856, NewCertificates0245.C7857, NewCertificates0245.C7858, NewCertificates0245.C7859, NewCertificates0245.C7860, NewCertificates0245.C7861, NewCertificates0245.C7862, NewCertificates0245.C7863, NewCertificates0245.C7864, NewCertificates0245.C7865, NewCertificates0245.C7866, NewCertificates0245.C7867}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,4)}
theorem doubled_enumeration : ((supportEdges 1597173136411901968).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1597173136411901968 D i ∧ offSum 1597173136411901968 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1597173136411901968 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1597173136411901968 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1597173136411901968 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1597173136411901968 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport169
