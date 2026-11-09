import SignedCatalogue
import NewCertificates0259
import NewCertificates0260
import NewCertificates0261
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport178
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 3, 6, 4, 5, 7, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0259.C8308, NewCertificates0259.C8309, NewCertificates0259.C8310, NewCertificates0259.C8311, NewCertificates0259.C8312, NewCertificates0259.C8313, NewCertificates0259.C8314, NewCertificates0259.C8315, NewCertificates0259.C8316, NewCertificates0259.C8317, NewCertificates0259.C8318, NewCertificates0259.C8319, NewCertificates0260.C8320, NewCertificates0260.C8321, NewCertificates0260.C8322, NewCertificates0260.C8323, NewCertificates0260.C8324, NewCertificates0260.C8325, NewCertificates0260.C8326, NewCertificates0260.C8327, NewCertificates0260.C8328, NewCertificates0260.C8329, NewCertificates0260.C8330, NewCertificates0260.C8331, NewCertificates0260.C8332, NewCertificates0260.C8333, NewCertificates0260.C8334, NewCertificates0260.C8335, NewCertificates0260.C8336, NewCertificates0260.C8337, NewCertificates0260.C8338, NewCertificates0260.C8339, NewCertificates0260.C8340, NewCertificates0260.C8341, NewCertificates0260.C8342, NewCertificates0260.C8343, NewCertificates0260.C8344, NewCertificates0260.C8345, NewCertificates0260.C8346, NewCertificates0260.C8347, NewCertificates0260.C8348, NewCertificates0260.C8349, NewCertificates0260.C8350, NewCertificates0260.C8351, NewCertificates0261.C8352, NewCertificates0261.C8353, NewCertificates0261.C8354, NewCertificates0261.C8355, NewCertificates0261.C8356, NewCertificates0261.C8357, NewCertificates0261.C8358, NewCertificates0261.C8359, NewCertificates0261.C8360, NewCertificates0261.C8361, NewCertificates0261.C8362, NewCertificates0261.C8363, NewCertificates0261.C8364, NewCertificates0261.C8365, NewCertificates0261.C8366, NewCertificates0261.C8367, NewCertificates0261.C8368, NewCertificates0261.C8369, NewCertificates0261.C8370, NewCertificates0261.C8371, NewCertificates0261.C8372, NewCertificates0261.C8373, NewCertificates0261.C8374, NewCertificates0261.C8375, NewCertificates0261.C8376, NewCertificates0261.C8377, NewCertificates0261.C8378, NewCertificates0261.C8379}
def U0 : QuotientMatrix := !![2, 0, 0, 1, 0, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 1, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 2, 0, 0, 0, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 2, 0, 0, 0, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,3), (1,2)}
theorem doubled_enumeration : ((supportEdges 3762987150258340872).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3762987150258340872 D i ∧ offSum 3762987150258340872 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 3762987150258340872 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3762987150258340872 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3762987150258340872 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 3762987150258340872 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3762987150258340872 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3762987150258340872 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport178
