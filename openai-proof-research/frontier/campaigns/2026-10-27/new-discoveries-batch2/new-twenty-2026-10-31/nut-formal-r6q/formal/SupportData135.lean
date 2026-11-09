import SignedCatalogue
import NewCertificates0198
import NewCertificates0199
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport135
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 4, 5, 2, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0198.C6356, NewCertificates0198.C6357, NewCertificates0198.C6358, NewCertificates0198.C6359, NewCertificates0198.C6360, NewCertificates0198.C6361, NewCertificates0198.C6362, NewCertificates0198.C6363, NewCertificates0198.C6364, NewCertificates0198.C6365, NewCertificates0198.C6366, NewCertificates0198.C6367, NewCertificates0199.C6368, NewCertificates0199.C6369, NewCertificates0199.C6370, NewCertificates0199.C6371, NewCertificates0199.C6372, NewCertificates0199.C6373, NewCertificates0199.C6374, NewCertificates0199.C6375, NewCertificates0199.C6376, NewCertificates0199.C6377, NewCertificates0199.C6378, NewCertificates0199.C6379, NewCertificates0199.C6380, NewCertificates0199.C6381, NewCertificates0199.C6382, NewCertificates0199.C6383, NewCertificates0199.C6384, NewCertificates0199.C6385, NewCertificates0199.C6386, NewCertificates0199.C6387}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 950631579435675840).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950631579435675840 D i ∧ offSum 950631579435675840 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 950631579435675840 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 950631579435675840 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950631579435675840 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950631579435675840 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport135
