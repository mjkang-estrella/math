import SignedCatalogue
import NewCertificates0241
import NewCertificates0242
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport165
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 7, 2, 3, 1, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 2]
def matrices : Finset QuotientMatrix := {NewCertificates0241.C7716, NewCertificates0241.C7717, NewCertificates0241.C7718, NewCertificates0241.C7719, NewCertificates0241.C7720, NewCertificates0241.C7721, NewCertificates0241.C7722, NewCertificates0241.C7723, NewCertificates0241.C7724, NewCertificates0241.C7725, NewCertificates0241.C7726, NewCertificates0241.C7727, NewCertificates0241.C7728, NewCertificates0241.C7729, NewCertificates0241.C7730, NewCertificates0241.C7731, NewCertificates0241.C7732, NewCertificates0241.C7733, NewCertificates0241.C7734, NewCertificates0241.C7735, NewCertificates0241.C7736, NewCertificates0241.C7737, NewCertificates0241.C7738, NewCertificates0241.C7739, NewCertificates0241.C7740, NewCertificates0241.C7741, NewCertificates0241.C7742, NewCertificates0241.C7743, NewCertificates0242.C7744, NewCertificates0242.C7745, NewCertificates0242.C7746, NewCertificates0242.C7747}
def U0 : QuotientMatrix := !![0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 509765795185217760).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 509765795185217760 D i ∧ offSum 509765795185217760 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 509765795185217760 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 509765795185217760 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 509765795185217760 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport165
