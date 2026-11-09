import SignedCatalogue
import NewCertificates0197
import NewCertificates0198
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport134
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 3, 5, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0197.C6324, NewCertificates0197.C6325, NewCertificates0197.C6326, NewCertificates0197.C6327, NewCertificates0197.C6328, NewCertificates0197.C6329, NewCertificates0197.C6330, NewCertificates0197.C6331, NewCertificates0197.C6332, NewCertificates0197.C6333, NewCertificates0197.C6334, NewCertificates0197.C6335, NewCertificates0198.C6336, NewCertificates0198.C6337, NewCertificates0198.C6338, NewCertificates0198.C6339, NewCertificates0198.C6340, NewCertificates0198.C6341, NewCertificates0198.C6342, NewCertificates0198.C6343, NewCertificates0198.C6344, NewCertificates0198.C6345, NewCertificates0198.C6346, NewCertificates0198.C6347, NewCertificates0198.C6348, NewCertificates0198.C6349, NewCertificates0198.C6350, NewCertificates0198.C6351, NewCertificates0198.C6352, NewCertificates0198.C6353, NewCertificates0198.C6354, NewCertificates0198.C6355}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 940432270339092672).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 940432270339092672 D i ∧ offSum 940432270339092672 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 940432270339092672 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 940432270339092672 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 940432270339092672 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport134
