import SignedCatalogue
import NewCertificates0257
import NewCertificates0258
import NewCertificates0259
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport177
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 4, 5, 6, 7, 2, 1, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0257.C8236, NewCertificates0257.C8237, NewCertificates0257.C8238, NewCertificates0257.C8239, NewCertificates0257.C8240, NewCertificates0257.C8241, NewCertificates0257.C8242, NewCertificates0257.C8243, NewCertificates0257.C8244, NewCertificates0257.C8245, NewCertificates0257.C8246, NewCertificates0257.C8247, NewCertificates0257.C8248, NewCertificates0257.C8249, NewCertificates0257.C8250, NewCertificates0257.C8251, NewCertificates0257.C8252, NewCertificates0257.C8253, NewCertificates0257.C8254, NewCertificates0257.C8255, NewCertificates0258.C8256, NewCertificates0258.C8257, NewCertificates0258.C8258, NewCertificates0258.C8259, NewCertificates0258.C8260, NewCertificates0258.C8261, NewCertificates0258.C8262, NewCertificates0258.C8263, NewCertificates0258.C8264, NewCertificates0258.C8265, NewCertificates0258.C8266, NewCertificates0258.C8267, NewCertificates0258.C8268, NewCertificates0258.C8269, NewCertificates0258.C8270, NewCertificates0258.C8271, NewCertificates0258.C8272, NewCertificates0258.C8273, NewCertificates0258.C8274, NewCertificates0258.C8275, NewCertificates0258.C8276, NewCertificates0258.C8277, NewCertificates0258.C8278, NewCertificates0258.C8279, NewCertificates0258.C8280, NewCertificates0258.C8281, NewCertificates0258.C8282, NewCertificates0258.C8283, NewCertificates0258.C8284, NewCertificates0258.C8285, NewCertificates0258.C8286, NewCertificates0258.C8287, NewCertificates0259.C8288, NewCertificates0259.C8289, NewCertificates0259.C8290, NewCertificates0259.C8291, NewCertificates0259.C8292, NewCertificates0259.C8293, NewCertificates0259.C8294, NewCertificates0259.C8295, NewCertificates0259.C8296, NewCertificates0259.C8297, NewCertificates0259.C8298, NewCertificates0259.C8299, NewCertificates0259.C8300, NewCertificates0259.C8301, NewCertificates0259.C8302, NewCertificates0259.C8303, NewCertificates0259.C8304, NewCertificates0259.C8305, NewCertificates0259.C8306, NewCertificates0259.C8307}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(0,4), (1,3)}
def D5 : Finset (Fin 8 × Fin 8) := {(0,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7108034952155400208).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7108034952155400208 D i ∧ offSum 7108034952155400208 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 7108034952155400208 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7108034952155400208 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7108034952155400208 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7108034952155400208 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 7108034952155400208 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 7108034952155400208 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7108034952155400208 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7108034952155400208 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport177
