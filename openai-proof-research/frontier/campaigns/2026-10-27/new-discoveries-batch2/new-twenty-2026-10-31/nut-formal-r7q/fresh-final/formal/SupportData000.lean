import SignedCatalogue
import NewCertificates0000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport000
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 4, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0000.C0, NewCertificates0000.C1, NewCertificates0000.C2, NewCertificates0000.C3, NewCertificates0000.C4, NewCertificates0000.C5, NewCertificates0000.C6, NewCertificates0000.C7, NewCertificates0000.C8, NewCertificates0000.C9, NewCertificates0000.C10, NewCertificates0000.C11, NewCertificates0000.C12, NewCertificates0000.C13, NewCertificates0000.C14, NewCertificates0000.C15, NewCertificates0000.C16, NewCertificates0000.C17, NewCertificates0000.C18, NewCertificates0000.C19, NewCertificates0000.C20, NewCertificates0000.C21, NewCertificates0000.C22, NewCertificates0000.C23, NewCertificates0000.C24, NewCertificates0000.C25, NewCertificates0000.C26, NewCertificates0000.C27, NewCertificates0000.C28, NewCertificates0000.C29, NewCertificates0000.C30, NewCertificates0000.C31}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 2534629527238246528).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2534629527238246528 D i ∧ offSum 2534629527238246528 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 2534629527238246528 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2534629527238246528 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2534629527238246528 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport000
