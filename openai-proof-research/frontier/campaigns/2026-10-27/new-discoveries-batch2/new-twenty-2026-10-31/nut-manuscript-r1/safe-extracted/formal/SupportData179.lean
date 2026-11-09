import SignedCatalogue
import NewCertificates0261
import NewCertificates0262
import NewCertificates0263
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport179
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 3, 7, 5, 1, 4, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0261.C8380, NewCertificates0261.C8381, NewCertificates0261.C8382, NewCertificates0261.C8383, NewCertificates0262.C8384, NewCertificates0262.C8385, NewCertificates0262.C8386, NewCertificates0262.C8387, NewCertificates0262.C8388, NewCertificates0262.C8389, NewCertificates0262.C8390, NewCertificates0262.C8391, NewCertificates0262.C8392, NewCertificates0262.C8393, NewCertificates0262.C8394, NewCertificates0262.C8395, NewCertificates0262.C8396, NewCertificates0262.C8397, NewCertificates0262.C8398, NewCertificates0262.C8399, NewCertificates0262.C8400, NewCertificates0262.C8401, NewCertificates0262.C8402, NewCertificates0262.C8403, NewCertificates0262.C8404, NewCertificates0262.C8405, NewCertificates0262.C8406, NewCertificates0262.C8407, NewCertificates0262.C8408, NewCertificates0262.C8409, NewCertificates0262.C8410, NewCertificates0262.C8411, NewCertificates0262.C8412, NewCertificates0262.C8413, NewCertificates0262.C8414, NewCertificates0262.C8415, NewCertificates0263.C8416, NewCertificates0263.C8417, NewCertificates0263.C8418, NewCertificates0263.C8419, NewCertificates0263.C8420, NewCertificates0263.C8421, NewCertificates0263.C8422, NewCertificates0263.C8423, NewCertificates0263.C8424, NewCertificates0263.C8425, NewCertificates0263.C8426, NewCertificates0263.C8427, NewCertificates0263.C8428, NewCertificates0263.C8429, NewCertificates0263.C8430, NewCertificates0263.C8431, NewCertificates0263.C8432, NewCertificates0263.C8433, NewCertificates0263.C8434, NewCertificates0263.C8435}
def U0 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U3 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,3), (1,2)}
theorem doubled_enumeration : ((supportEdges 1383828705163510920).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1383828705163510920 D i ∧ offSum 1383828705163510920 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 1383828705163510920 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1383828705163510920 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1383828705163510920 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1383828705163510920 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1383828705163510920 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1383828705163510920 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport179
