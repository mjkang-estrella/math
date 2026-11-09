import SignedCatalogue
import NewCertificates0022
import NewCertificates0023
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport015
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 5, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0022.C720, NewCertificates0022.C721, NewCertificates0022.C722, NewCertificates0022.C723, NewCertificates0022.C724, NewCertificates0022.C725, NewCertificates0022.C726, NewCertificates0022.C727, NewCertificates0022.C728, NewCertificates0022.C729, NewCertificates0022.C730, NewCertificates0022.C731, NewCertificates0022.C732, NewCertificates0022.C733, NewCertificates0022.C734, NewCertificates0022.C735, NewCertificates0023.C736, NewCertificates0023.C737, NewCertificates0023.C738, NewCertificates0023.C739, NewCertificates0023.C740, NewCertificates0023.C741, NewCertificates0023.C742, NewCertificates0023.C743, NewCertificates0023.C744, NewCertificates0023.C745, NewCertificates0023.C746, NewCertificates0023.C747, NewCertificates0023.C748, NewCertificates0023.C749, NewCertificates0023.C750, NewCertificates0023.C751}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1377007336083718272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1377007336083718272 D i ∧ offSum 1377007336083718272 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1377007336083718272 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1377007336083718272 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1377007336083718272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport015
