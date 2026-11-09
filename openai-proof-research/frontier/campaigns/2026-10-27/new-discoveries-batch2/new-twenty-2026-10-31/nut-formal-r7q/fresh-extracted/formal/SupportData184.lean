import SignedCatalogue
import NewCertificates0270
import NewCertificates0271
import NewCertificates0272
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport184
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 2, 5, 3, 4, 6, 7, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0270.C8668, NewCertificates0270.C8669, NewCertificates0270.C8670, NewCertificates0270.C8671, NewCertificates0271.C8672, NewCertificates0271.C8673, NewCertificates0271.C8674, NewCertificates0271.C8675, NewCertificates0271.C8676, NewCertificates0271.C8677, NewCertificates0271.C8678, NewCertificates0271.C8679, NewCertificates0271.C8680, NewCertificates0271.C8681, NewCertificates0271.C8682, NewCertificates0271.C8683, NewCertificates0271.C8684, NewCertificates0271.C8685, NewCertificates0271.C8686, NewCertificates0271.C8687, NewCertificates0271.C8688, NewCertificates0271.C8689, NewCertificates0271.C8690, NewCertificates0271.C8691, NewCertificates0271.C8692, NewCertificates0271.C8693, NewCertificates0271.C8694, NewCertificates0271.C8695, NewCertificates0271.C8696, NewCertificates0271.C8697, NewCertificates0271.C8698, NewCertificates0271.C8699, NewCertificates0271.C8700, NewCertificates0271.C8701, NewCertificates0271.C8702, NewCertificates0271.C8703, NewCertificates0272.C8704, NewCertificates0272.C8705, NewCertificates0272.C8706, NewCertificates0272.C8707, NewCertificates0272.C8708, NewCertificates0272.C8709, NewCertificates0272.C8710, NewCertificates0272.C8711, NewCertificates0272.C8712, NewCertificates0272.C8713, NewCertificates0272.C8714, NewCertificates0272.C8715}
def U0 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 1, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 2, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,2)}
theorem doubled_enumeration : ((supportEdges 1880847546539163652).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1880847546539163652 D i ∧ offSum 1880847546539163652 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1880847546539163652 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1880847546539163652 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1880847546539163652 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1880847546539163652 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport184
