import SignedCatalogue
import NewCertificates0200
import NewCertificates0201
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport137
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 3, 1, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0200.C6420, NewCertificates0200.C6421, NewCertificates0200.C6422, NewCertificates0200.C6423, NewCertificates0200.C6424, NewCertificates0200.C6425, NewCertificates0200.C6426, NewCertificates0200.C6427, NewCertificates0200.C6428, NewCertificates0200.C6429, NewCertificates0200.C6430, NewCertificates0200.C6431, NewCertificates0201.C6432, NewCertificates0201.C6433, NewCertificates0201.C6434, NewCertificates0201.C6435, NewCertificates0201.C6436, NewCertificates0201.C6437, NewCertificates0201.C6438, NewCertificates0201.C6439, NewCertificates0201.C6440, NewCertificates0201.C6441, NewCertificates0201.C6442, NewCertificates0201.C6443, NewCertificates0201.C6444, NewCertificates0201.C6445, NewCertificates0201.C6446, NewCertificates0201.C6447, NewCertificates0201.C6448, NewCertificates0201.C6449, NewCertificates0201.C6450, NewCertificates0201.C6451}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 942688707977687232).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 942688707977687232 D i ∧ offSum 942688707977687232 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 942688707977687232 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 942688707977687232 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 942688707977687232 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport137
