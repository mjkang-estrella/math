import SignedCatalogue
import NewCertificates0206
import NewCertificates0207
import NewCertificates0208
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport143
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 4, 5, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0206.C6612, NewCertificates0206.C6613, NewCertificates0206.C6614, NewCertificates0206.C6615, NewCertificates0206.C6616, NewCertificates0206.C6617, NewCertificates0206.C6618, NewCertificates0206.C6619, NewCertificates0206.C6620, NewCertificates0206.C6621, NewCertificates0206.C6622, NewCertificates0206.C6623, NewCertificates0207.C6624, NewCertificates0207.C6625, NewCertificates0207.C6626, NewCertificates0207.C6627, NewCertificates0207.C6628, NewCertificates0207.C6629, NewCertificates0207.C6630, NewCertificates0207.C6631, NewCertificates0207.C6632, NewCertificates0207.C6633, NewCertificates0207.C6634, NewCertificates0207.C6635, NewCertificates0207.C6636, NewCertificates0207.C6637, NewCertificates0207.C6638, NewCertificates0207.C6639, NewCertificates0207.C6640, NewCertificates0207.C6641, NewCertificates0207.C6642, NewCertificates0207.C6643, NewCertificates0207.C6644, NewCertificates0207.C6645, NewCertificates0207.C6646, NewCertificates0207.C6647, NewCertificates0207.C6648, NewCertificates0207.C6649, NewCertificates0207.C6650, NewCertificates0207.C6651, NewCertificates0207.C6652, NewCertificates0207.C6653, NewCertificates0207.C6654, NewCertificates0207.C6655, NewCertificates0208.C6656, NewCertificates0208.C6657, NewCertificates0208.C6658, NewCertificates0208.C6659}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 1382979881732180160).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1382979881732180160 D i ∧ offSum 1382979881732180160 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 1382979881732180160 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1382979881732180160 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1382979881732180160 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1382979881732180160 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1382979881732180160 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport143
