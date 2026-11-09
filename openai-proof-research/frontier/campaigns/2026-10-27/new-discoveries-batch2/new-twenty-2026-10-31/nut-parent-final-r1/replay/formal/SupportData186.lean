import SignedCatalogue
import NewCertificates0273
import NewCertificates0274
import NewCertificates0275
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport186
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 2, 5, 3, 4, 7, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0273.C8764, NewCertificates0273.C8765, NewCertificates0273.C8766, NewCertificates0273.C8767, NewCertificates0274.C8768, NewCertificates0274.C8769, NewCertificates0274.C8770, NewCertificates0274.C8771, NewCertificates0274.C8772, NewCertificates0274.C8773, NewCertificates0274.C8774, NewCertificates0274.C8775, NewCertificates0274.C8776, NewCertificates0274.C8777, NewCertificates0274.C8778, NewCertificates0274.C8779, NewCertificates0274.C8780, NewCertificates0274.C8781, NewCertificates0274.C8782, NewCertificates0274.C8783, NewCertificates0274.C8784, NewCertificates0274.C8785, NewCertificates0274.C8786, NewCertificates0274.C8787, NewCertificates0274.C8788, NewCertificates0274.C8789, NewCertificates0274.C8790, NewCertificates0274.C8791, NewCertificates0274.C8792, NewCertificates0274.C8793, NewCertificates0274.C8794, NewCertificates0274.C8795, NewCertificates0274.C8796, NewCertificates0274.C8797, NewCertificates0274.C8798, NewCertificates0274.C8799, NewCertificates0275.C8800, NewCertificates0275.C8801, NewCertificates0275.C8802, NewCertificates0275.C8803, NewCertificates0275.C8804, NewCertificates0275.C8805, NewCertificates0275.C8806, NewCertificates0275.C8807, NewCertificates0275.C8808, NewCertificates0275.C8809, NewCertificates0275.C8810, NewCertificates0275.C8811}
def U0 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,2)}
theorem doubled_enumeration : ((supportEdges 5373388541363601412).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5373388541363601412 D i ∧ offSum 5373388541363601412 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 5373388541363601412 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5373388541363601412 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5373388541363601412 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5373388541363601412 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport186
