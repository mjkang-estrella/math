import SignedCatalogue
import NewCertificates0265
import NewCertificates0266
import NewCertificates0267
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport181
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 3, 7, 4, 5, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0265.C8492, NewCertificates0265.C8493, NewCertificates0265.C8494, NewCertificates0265.C8495, NewCertificates0265.C8496, NewCertificates0265.C8497, NewCertificates0265.C8498, NewCertificates0265.C8499, NewCertificates0265.C8500, NewCertificates0265.C8501, NewCertificates0265.C8502, NewCertificates0265.C8503, NewCertificates0265.C8504, NewCertificates0265.C8505, NewCertificates0265.C8506, NewCertificates0265.C8507, NewCertificates0265.C8508, NewCertificates0265.C8509, NewCertificates0265.C8510, NewCertificates0265.C8511, NewCertificates0266.C8512, NewCertificates0266.C8513, NewCertificates0266.C8514, NewCertificates0266.C8515, NewCertificates0266.C8516, NewCertificates0266.C8517, NewCertificates0266.C8518, NewCertificates0266.C8519, NewCertificates0266.C8520, NewCertificates0266.C8521, NewCertificates0266.C8522, NewCertificates0266.C8523, NewCertificates0266.C8524, NewCertificates0266.C8525, NewCertificates0266.C8526, NewCertificates0266.C8527, NewCertificates0266.C8528, NewCertificates0266.C8529, NewCertificates0266.C8530, NewCertificates0266.C8531, NewCertificates0266.C8532, NewCertificates0266.C8533, NewCertificates0266.C8534, NewCertificates0266.C8535, NewCertificates0266.C8536, NewCertificates0266.C8537, NewCertificates0266.C8538, NewCertificates0266.C8539, NewCertificates0266.C8540, NewCertificates0266.C8541, NewCertificates0266.C8542, NewCertificates0266.C8543, NewCertificates0267.C8544, NewCertificates0267.C8545, NewCertificates0267.C8546, NewCertificates0267.C8547}
def U0 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 1, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(0,3), (1,2)}
theorem doubled_enumeration : ((supportEdges 7030845142963733640).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7030845142963733640 D i ∧ offSum 7030845142963733640 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 7030845142963733640 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7030845142963733640 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7030845142963733640 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7030845142963733640 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7030845142963733640 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7030845142963733640 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport181
