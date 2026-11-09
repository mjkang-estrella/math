import SignedCatalogue
import NewCertificates0209
import NewCertificates0210
import NewCertificates0211
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport145
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 5, 4, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0209.C6708, NewCertificates0209.C6709, NewCertificates0209.C6710, NewCertificates0209.C6711, NewCertificates0209.C6712, NewCertificates0209.C6713, NewCertificates0209.C6714, NewCertificates0209.C6715, NewCertificates0209.C6716, NewCertificates0209.C6717, NewCertificates0209.C6718, NewCertificates0209.C6719, NewCertificates0210.C6720, NewCertificates0210.C6721, NewCertificates0210.C6722, NewCertificates0210.C6723, NewCertificates0210.C6724, NewCertificates0210.C6725, NewCertificates0210.C6726, NewCertificates0210.C6727, NewCertificates0210.C6728, NewCertificates0210.C6729, NewCertificates0210.C6730, NewCertificates0210.C6731, NewCertificates0210.C6732, NewCertificates0210.C6733, NewCertificates0210.C6734, NewCertificates0210.C6735, NewCertificates0210.C6736, NewCertificates0210.C6737, NewCertificates0210.C6738, NewCertificates0210.C6739, NewCertificates0210.C6740, NewCertificates0210.C6741, NewCertificates0210.C6742, NewCertificates0210.C6743, NewCertificates0210.C6744, NewCertificates0210.C6745, NewCertificates0210.C6746, NewCertificates0210.C6747, NewCertificates0210.C6748, NewCertificates0210.C6749, NewCertificates0210.C6750, NewCertificates0210.C6751, NewCertificates0211.C6752, NewCertificates0211.C6753, NewCertificates0211.C6754, NewCertificates0211.C6755}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 5882073452752939200).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5882073452752939200 D i ∧ offSum 5882073452752939200 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 5882073452752939200 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5882073452752939200 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5882073452752939200 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5882073452752939200 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5882073452752939200 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport145
