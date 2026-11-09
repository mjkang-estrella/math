import SignedCatalogue
import NewCertificates0173
import NewCertificates0174
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport115
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 5, 4, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0173.C5564, NewCertificates0173.C5565, NewCertificates0173.C5566, NewCertificates0173.C5567, NewCertificates0174.C5568, NewCertificates0174.C5569, NewCertificates0174.C5570, NewCertificates0174.C5571, NewCertificates0174.C5572, NewCertificates0174.C5573, NewCertificates0174.C5574, NewCertificates0174.C5575, NewCertificates0174.C5576, NewCertificates0174.C5577, NewCertificates0174.C5578, NewCertificates0174.C5579}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 1, 1, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1379030075893137600).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1379030075893137600 D i ∧ offSum 1379030075893137600 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1379030075893137600 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1379030075893137600 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1379030075893137600 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport115
