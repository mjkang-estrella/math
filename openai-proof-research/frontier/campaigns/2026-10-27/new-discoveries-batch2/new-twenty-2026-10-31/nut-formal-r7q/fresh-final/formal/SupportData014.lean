import SignedCatalogue
import NewCertificates0020
import NewCertificates0021
import NewCertificates0022
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport014
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 5, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0020.C664, NewCertificates0020.C665, NewCertificates0020.C666, NewCertificates0020.C667, NewCertificates0020.C668, NewCertificates0020.C669, NewCertificates0020.C670, NewCertificates0020.C671, NewCertificates0021.C672, NewCertificates0021.C673, NewCertificates0021.C674, NewCertificates0021.C675, NewCertificates0021.C676, NewCertificates0021.C677, NewCertificates0021.C678, NewCertificates0021.C679, NewCertificates0021.C680, NewCertificates0021.C681, NewCertificates0021.C682, NewCertificates0021.C683, NewCertificates0021.C684, NewCertificates0021.C685, NewCertificates0021.C686, NewCertificates0021.C687, NewCertificates0021.C688, NewCertificates0021.C689, NewCertificates0021.C690, NewCertificates0021.C691, NewCertificates0021.C692, NewCertificates0021.C693, NewCertificates0021.C694, NewCertificates0021.C695, NewCertificates0021.C696, NewCertificates0021.C697, NewCertificates0021.C698, NewCertificates0021.C699, NewCertificates0021.C700, NewCertificates0021.C701, NewCertificates0021.C702, NewCertificates0021.C703, NewCertificates0022.C704, NewCertificates0022.C705, NewCertificates0022.C706, NewCertificates0022.C707, NewCertificates0022.C708, NewCertificates0022.C709, NewCertificates0022.C710, NewCertificates0022.C711, NewCertificates0022.C712, NewCertificates0022.C713, NewCertificates0022.C714, NewCertificates0022.C715, NewCertificates0022.C716, NewCertificates0022.C717, NewCertificates0022.C718, NewCertificates0022.C719}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 520240834342322304).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 520240834342322304 D i ∧ offSum 520240834342322304 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 520240834342322304 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 520240834342322304 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 520240834342322304 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 520240834342322304 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 520240834342322304 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 520240834342322304 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport014
