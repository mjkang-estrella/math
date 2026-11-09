import SignedCatalogue
import NewCertificates0263
import NewCertificates0264
import NewCertificates0265
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport180
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 3, 7, 4, 5, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0263.C8436, NewCertificates0263.C8437, NewCertificates0263.C8438, NewCertificates0263.C8439, NewCertificates0263.C8440, NewCertificates0263.C8441, NewCertificates0263.C8442, NewCertificates0263.C8443, NewCertificates0263.C8444, NewCertificates0263.C8445, NewCertificates0263.C8446, NewCertificates0263.C8447, NewCertificates0264.C8448, NewCertificates0264.C8449, NewCertificates0264.C8450, NewCertificates0264.C8451, NewCertificates0264.C8452, NewCertificates0264.C8453, NewCertificates0264.C8454, NewCertificates0264.C8455, NewCertificates0264.C8456, NewCertificates0264.C8457, NewCertificates0264.C8458, NewCertificates0264.C8459, NewCertificates0264.C8460, NewCertificates0264.C8461, NewCertificates0264.C8462, NewCertificates0264.C8463, NewCertificates0264.C8464, NewCertificates0264.C8465, NewCertificates0264.C8466, NewCertificates0264.C8467, NewCertificates0264.C8468, NewCertificates0264.C8469, NewCertificates0264.C8470, NewCertificates0264.C8471, NewCertificates0264.C8472, NewCertificates0264.C8473, NewCertificates0264.C8474, NewCertificates0264.C8475, NewCertificates0264.C8476, NewCertificates0264.C8477, NewCertificates0264.C8478, NewCertificates0264.C8479, NewCertificates0265.C8480, NewCertificates0265.C8481, NewCertificates0265.C8482, NewCertificates0265.C8483, NewCertificates0265.C8484, NewCertificates0265.C8485, NewCertificates0265.C8486, NewCertificates0265.C8487, NewCertificates0265.C8488, NewCertificates0265.C8489, NewCertificates0265.C8490, NewCertificates0265.C8491}
def U0 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U3 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,3), (1,2)}
theorem doubled_enumeration : ((supportEdges 3545112220253963400).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545112220253963400 D i ∧ offSum 3545112220253963400 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 3545112220253963400 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3545112220253963400 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3545112220253963400 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 3545112220253963400 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545112220253963400 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545112220253963400 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport180
