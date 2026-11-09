import SignedCatalogue
import NewCertificates0272
import NewCertificates0273
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport185
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 2, 5, 4, 6, 3, 7, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0272.C8716, NewCertificates0272.C8717, NewCertificates0272.C8718, NewCertificates0272.C8719, NewCertificates0272.C8720, NewCertificates0272.C8721, NewCertificates0272.C8722, NewCertificates0272.C8723, NewCertificates0272.C8724, NewCertificates0272.C8725, NewCertificates0272.C8726, NewCertificates0272.C8727, NewCertificates0272.C8728, NewCertificates0272.C8729, NewCertificates0272.C8730, NewCertificates0272.C8731, NewCertificates0272.C8732, NewCertificates0272.C8733, NewCertificates0272.C8734, NewCertificates0272.C8735, NewCertificates0273.C8736, NewCertificates0273.C8737, NewCertificates0273.C8738, NewCertificates0273.C8739, NewCertificates0273.C8740, NewCertificates0273.C8741, NewCertificates0273.C8742, NewCertificates0273.C8743, NewCertificates0273.C8744, NewCertificates0273.C8745, NewCertificates0273.C8746, NewCertificates0273.C8747, NewCertificates0273.C8748, NewCertificates0273.C8749, NewCertificates0273.C8750, NewCertificates0273.C8751, NewCertificates0273.C8752, NewCertificates0273.C8753, NewCertificates0273.C8754, NewCertificates0273.C8755, NewCertificates0273.C8756, NewCertificates0273.C8757, NewCertificates0273.C8758, NewCertificates0273.C8759, NewCertificates0273.C8760, NewCertificates0273.C8761, NewCertificates0273.C8762, NewCertificates0273.C8763}
def U0 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,2)}
theorem doubled_enumeration : ((supportEdges 1885412478031085572).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1885412478031085572 D i ∧ offSum 1885412478031085572 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1885412478031085572 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1885412478031085572 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1885412478031085572 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1885412478031085572 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport185
