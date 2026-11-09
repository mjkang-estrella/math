import SignedCatalogue
import NewCertificates0011
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport007
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 3, 4, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0011.C352, NewCertificates0011.C353, NewCertificates0011.C354, NewCertificates0011.C355, NewCertificates0011.C356, NewCertificates0011.C357, NewCertificates0011.C358, NewCertificates0011.C359, NewCertificates0011.C360, NewCertificates0011.C361, NewCertificates0011.C362, NewCertificates0011.C363, NewCertificates0011.C364, NewCertificates0011.C365, NewCertificates0011.C366, NewCertificates0011.C367, NewCertificates0011.C368, NewCertificates0011.C369, NewCertificates0011.C370, NewCertificates0011.C371, NewCertificates0011.C372, NewCertificates0011.C373, NewCertificates0011.C374, NewCertificates0011.C375, NewCertificates0011.C376, NewCertificates0011.C377, NewCertificates0011.C378, NewCertificates0011.C379, NewCertificates0011.C380, NewCertificates0011.C381, NewCertificates0011.C382, NewCertificates0011.C383}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 2530064630374498432).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2530064630374498432 D i ∧ offSum 2530064630374498432 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 2530064630374498432 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2530064630374498432 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2530064630374498432 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport007
