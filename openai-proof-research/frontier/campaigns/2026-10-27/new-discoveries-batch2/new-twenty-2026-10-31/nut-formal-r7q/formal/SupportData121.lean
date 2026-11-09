import SignedCatalogue
import NewCertificates0180
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport121
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 1, 3, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0180.C5772, NewCertificates0180.C5773, NewCertificates0180.C5774, NewCertificates0180.C5775, NewCertificates0180.C5776, NewCertificates0180.C5777, NewCertificates0180.C5778, NewCertificates0180.C5779, NewCertificates0180.C5780, NewCertificates0180.C5781, NewCertificates0180.C5782, NewCertificates0180.C5783, NewCertificates0180.C5784, NewCertificates0180.C5785, NewCertificates0180.C5786, NewCertificates0180.C5787}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 798569147282792640).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 798569147282792640 D i ∧ offSum 798569147282792640 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 798569147282792640 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 798569147282792640 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 798569147282792640 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport121
