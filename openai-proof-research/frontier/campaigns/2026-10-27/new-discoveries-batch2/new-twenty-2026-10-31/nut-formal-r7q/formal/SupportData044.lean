import SignedCatalogue
import NewCertificates0068
import NewCertificates0069
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport044
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 5, 3, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0068.C2202, NewCertificates0068.C2203, NewCertificates0068.C2204, NewCertificates0068.C2205, NewCertificates0068.C2206, NewCertificates0068.C2207, NewCertificates0069.C2208, NewCertificates0069.C2209, NewCertificates0069.C2210, NewCertificates0069.C2211, NewCertificates0069.C2212, NewCertificates0069.C2213, NewCertificates0069.C2214, NewCertificates0069.C2215, NewCertificates0069.C2216, NewCertificates0069.C2217, NewCertificates0069.C2218, NewCertificates0069.C2219, NewCertificates0069.C2220, NewCertificates0069.C2221, NewCertificates0069.C2222, NewCertificates0069.C2223, NewCertificates0069.C2224, NewCertificates0069.C2225, NewCertificates0069.C2226, NewCertificates0069.C2227, NewCertificates0069.C2228, NewCertificates0069.C2229, NewCertificates0069.C2230, NewCertificates0069.C2231, NewCertificates0069.C2232, NewCertificates0069.C2233}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1525128886836281472).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1525128886836281472 D i ∧ offSum 1525128886836281472 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1525128886836281472 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1525128886836281472 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1525128886836281472 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport044
