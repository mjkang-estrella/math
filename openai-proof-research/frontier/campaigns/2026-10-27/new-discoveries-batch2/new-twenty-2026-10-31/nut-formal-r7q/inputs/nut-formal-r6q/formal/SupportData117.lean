import SignedCatalogue
import NewCertificates0175
import NewCertificates0176
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport117
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 4, 5, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0175.C5612, NewCertificates0175.C5613, NewCertificates0175.C5614, NewCertificates0175.C5615, NewCertificates0175.C5616, NewCertificates0175.C5617, NewCertificates0175.C5618, NewCertificates0175.C5619, NewCertificates0175.C5620, NewCertificates0175.C5621, NewCertificates0175.C5622, NewCertificates0175.C5623, NewCertificates0175.C5624, NewCertificates0175.C5625, NewCertificates0175.C5626, NewCertificates0175.C5627, NewCertificates0175.C5628, NewCertificates0175.C5629, NewCertificates0175.C5630, NewCertificates0175.C5631, NewCertificates0176.C5632, NewCertificates0176.C5633, NewCertificates0176.C5634, NewCertificates0176.C5635, NewCertificates0176.C5636, NewCertificates0176.C5637, NewCertificates0176.C5638, NewCertificates0176.C5639, NewCertificates0176.C5640, NewCertificates0176.C5641, NewCertificates0176.C5642, NewCertificates0176.C5643}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1374474060283035840).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1374474060283035840 D i ∧ offSum 1374474060283035840 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1374474060283035840 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1374474060283035840 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1374474060283035840 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1374474060283035840 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport117
