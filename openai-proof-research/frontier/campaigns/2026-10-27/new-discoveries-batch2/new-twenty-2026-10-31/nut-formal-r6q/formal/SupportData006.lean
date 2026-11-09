import SignedCatalogue
import NewCertificates0010
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport006
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 5, 4, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0010.C320, NewCertificates0010.C321, NewCertificates0010.C322, NewCertificates0010.C323, NewCertificates0010.C324, NewCertificates0010.C325, NewCertificates0010.C326, NewCertificates0010.C327, NewCertificates0010.C328, NewCertificates0010.C329, NewCertificates0010.C330, NewCertificates0010.C331, NewCertificates0010.C332, NewCertificates0010.C333, NewCertificates0010.C334, NewCertificates0010.C335, NewCertificates0010.C336, NewCertificates0010.C337, NewCertificates0010.C338, NewCertificates0010.C339, NewCertificates0010.C340, NewCertificates0010.C341, NewCertificates0010.C342, NewCertificates0010.C343, NewCertificates0010.C344, NewCertificates0010.C345, NewCertificates0010.C346, NewCertificates0010.C347, NewCertificates0010.C348, NewCertificates0010.C349, NewCertificates0010.C350, NewCertificates0010.C351}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 807367405234847872).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 807367405234847872 D i ∧ offSum 807367405234847872 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 807367405234847872 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 807367405234847872 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 807367405234847872 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport006
