import SignedCatalogue
import NewCertificates0023
import NewCertificates0024
import NewCertificates0025
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport016
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 6, 2, 3, 5, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0023.C752, NewCertificates0023.C753, NewCertificates0023.C754, NewCertificates0023.C755, NewCertificates0023.C756, NewCertificates0023.C757, NewCertificates0023.C758, NewCertificates0023.C759, NewCertificates0023.C760, NewCertificates0023.C761, NewCertificates0023.C762, NewCertificates0023.C763, NewCertificates0023.C764, NewCertificates0023.C765, NewCertificates0023.C766, NewCertificates0023.C767, NewCertificates0024.C768, NewCertificates0024.C769, NewCertificates0024.C770, NewCertificates0024.C771, NewCertificates0024.C772, NewCertificates0024.C773, NewCertificates0024.C774, NewCertificates0024.C775, NewCertificates0024.C776, NewCertificates0024.C777, NewCertificates0024.C778, NewCertificates0024.C779, NewCertificates0024.C780, NewCertificates0024.C781, NewCertificates0024.C782, NewCertificates0024.C783, NewCertificates0024.C784, NewCertificates0024.C785, NewCertificates0024.C786, NewCertificates0024.C787, NewCertificates0024.C788, NewCertificates0024.C789, NewCertificates0024.C790, NewCertificates0024.C791, NewCertificates0024.C792, NewCertificates0024.C793, NewCertificates0024.C794, NewCertificates0024.C795, NewCertificates0024.C796, NewCertificates0024.C797, NewCertificates0024.C798, NewCertificates0024.C799, NewCertificates0025.C800, NewCertificates0025.C801, NewCertificates0025.C802, NewCertificates0025.C803, NewCertificates0025.C804, NewCertificates0025.C805, NewCertificates0025.C806, NewCertificates0025.C807, NewCertificates0025.C808, NewCertificates0025.C809, NewCertificates0025.C810, NewCertificates0025.C811, NewCertificates0025.C812, NewCertificates0025.C813, NewCertificates0025.C814, NewCertificates0025.C815, NewCertificates0025.C816, NewCertificates0025.C817, NewCertificates0025.C818, NewCertificates0025.C819, NewCertificates0025.C820, NewCertificates0025.C821, NewCertificates0025.C822, NewCertificates0025.C823}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 4867287460660412544).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4867287460660412544 D i ∧ offSum 4867287460660412544 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 4867287460660412544 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4867287460660412544 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4867287460660412544 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4867287460660412544 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 4867287460660412544 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4867287460660412544 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4867287460660412544 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport016
