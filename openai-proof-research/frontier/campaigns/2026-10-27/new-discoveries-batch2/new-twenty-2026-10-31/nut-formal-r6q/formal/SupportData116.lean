import SignedCatalogue
import NewCertificates0174
import NewCertificates0175
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport116
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 3, 2, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0174.C5580, NewCertificates0174.C5581, NewCertificates0174.C5582, NewCertificates0174.C5583, NewCertificates0174.C5584, NewCertificates0174.C5585, NewCertificates0174.C5586, NewCertificates0174.C5587, NewCertificates0174.C5588, NewCertificates0174.C5589, NewCertificates0174.C5590, NewCertificates0174.C5591, NewCertificates0174.C5592, NewCertificates0174.C5593, NewCertificates0174.C5594, NewCertificates0174.C5595, NewCertificates0174.C5596, NewCertificates0174.C5597, NewCertificates0174.C5598, NewCertificates0174.C5599, NewCertificates0175.C5600, NewCertificates0175.C5601, NewCertificates0175.C5602, NewCertificates0175.C5603, NewCertificates0175.C5604, NewCertificates0175.C5605, NewCertificates0175.C5606, NewCertificates0175.C5607, NewCertificates0175.C5608, NewCertificates0175.C5609, NewCertificates0175.C5610, NewCertificates0175.C5611}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 507530360204083392).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507530360204083392 D i ∧ offSum 507530360204083392 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 507530360204083392 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507530360204083392 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507530360204083392 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport116
