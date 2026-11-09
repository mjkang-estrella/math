import SignedCatalogue
import NewCertificates0208
import NewCertificates0209
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport144
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 4, 5, 2, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0208.C6660, NewCertificates0208.C6661, NewCertificates0208.C6662, NewCertificates0208.C6663, NewCertificates0208.C6664, NewCertificates0208.C6665, NewCertificates0208.C6666, NewCertificates0208.C6667, NewCertificates0208.C6668, NewCertificates0208.C6669, NewCertificates0208.C6670, NewCertificates0208.C6671, NewCertificates0208.C6672, NewCertificates0208.C6673, NewCertificates0208.C6674, NewCertificates0208.C6675, NewCertificates0208.C6676, NewCertificates0208.C6677, NewCertificates0208.C6678, NewCertificates0208.C6679, NewCertificates0208.C6680, NewCertificates0208.C6681, NewCertificates0208.C6682, NewCertificates0208.C6683, NewCertificates0208.C6684, NewCertificates0208.C6685, NewCertificates0208.C6686, NewCertificates0208.C6687, NewCertificates0209.C6688, NewCertificates0209.C6689, NewCertificates0209.C6690, NewCertificates0209.C6691, NewCertificates0209.C6692, NewCertificates0209.C6693, NewCertificates0209.C6694, NewCertificates0209.C6695, NewCertificates0209.C6696, NewCertificates0209.C6697, NewCertificates0209.C6698, NewCertificates0209.C6699, NewCertificates0209.C6700, NewCertificates0209.C6701, NewCertificates0209.C6702, NewCertificates0209.C6703, NewCertificates0209.C6704, NewCertificates0209.C6705, NewCertificates0209.C6706, NewCertificates0209.C6707}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 3544828528888916160).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3544828528888916160 D i ∧ offSum 3544828528888916160 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 3544828528888916160 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3544828528888916160 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3544828528888916160 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3544828528888916160 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3544828528888916160 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport144
