import SignedCatalogue
import NewCertificates0211
import NewCertificates0212
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport146
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 2, 3, 7, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0211.C6756, NewCertificates0211.C6757, NewCertificates0211.C6758, NewCertificates0211.C6759, NewCertificates0211.C6760, NewCertificates0211.C6761, NewCertificates0211.C6762, NewCertificates0211.C6763, NewCertificates0211.C6764, NewCertificates0211.C6765, NewCertificates0211.C6766, NewCertificates0211.C6767, NewCertificates0211.C6768, NewCertificates0211.C6769, NewCertificates0211.C6770, NewCertificates0211.C6771, NewCertificates0211.C6772, NewCertificates0211.C6773, NewCertificates0211.C6774, NewCertificates0211.C6775, NewCertificates0211.C6776, NewCertificates0211.C6777, NewCertificates0211.C6778, NewCertificates0211.C6779, NewCertificates0211.C6780, NewCertificates0211.C6781, NewCertificates0211.C6782, NewCertificates0211.C6783, NewCertificates0212.C6784, NewCertificates0212.C6785, NewCertificates0212.C6786, NewCertificates0212.C6787, NewCertificates0212.C6788, NewCertificates0212.C6789, NewCertificates0212.C6790, NewCertificates0212.C6791}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 1, 0, 0, 1, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
theorem doubled_enumeration : ((supportEdges 2030069561872617504).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2030069561872617504 D i ∧ offSum 2030069561872617504 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2030069561872617504 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2030069561872617504 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2030069561872617504 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2030069561872617504 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2030069561872617504 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2030069561872617504 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport146
