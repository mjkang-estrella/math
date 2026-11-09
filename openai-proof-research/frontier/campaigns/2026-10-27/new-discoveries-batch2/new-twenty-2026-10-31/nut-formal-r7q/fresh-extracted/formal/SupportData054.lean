import SignedCatalogue
import NewCertificates0080
import NewCertificates0081
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport054
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0080.C2586, NewCertificates0080.C2587, NewCertificates0080.C2588, NewCertificates0080.C2589, NewCertificates0080.C2590, NewCertificates0080.C2591, NewCertificates0081.C2592, NewCertificates0081.C2593, NewCertificates0081.C2594, NewCertificates0081.C2595, NewCertificates0081.C2596, NewCertificates0081.C2597, NewCertificates0081.C2598, NewCertificates0081.C2599, NewCertificates0081.C2600, NewCertificates0081.C2601}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 511752707923558528).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 511752707923558528 D i ∧ offSum 511752707923558528 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 511752707923558528 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 511752707923558528 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 511752707923558528 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport054
