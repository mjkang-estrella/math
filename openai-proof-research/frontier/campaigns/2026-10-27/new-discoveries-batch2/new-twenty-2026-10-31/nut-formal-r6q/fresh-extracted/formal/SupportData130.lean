import SignedCatalogue
import NewCertificates0193
import NewCertificates0194
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport130
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 5, 1, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0193.C6196, NewCertificates0193.C6197, NewCertificates0193.C6198, NewCertificates0193.C6199, NewCertificates0193.C6200, NewCertificates0193.C6201, NewCertificates0193.C6202, NewCertificates0193.C6203, NewCertificates0193.C6204, NewCertificates0193.C6205, NewCertificates0193.C6206, NewCertificates0193.C6207, NewCertificates0194.C6208, NewCertificates0194.C6209, NewCertificates0194.C6210, NewCertificates0194.C6211, NewCertificates0194.C6212, NewCertificates0194.C6213, NewCertificates0194.C6214, NewCertificates0194.C6215, NewCertificates0194.C6216, NewCertificates0194.C6217, NewCertificates0194.C6218, NewCertificates0194.C6219, NewCertificates0194.C6220, NewCertificates0194.C6221, NewCertificates0194.C6222, NewCertificates0194.C6223, NewCertificates0194.C6224, NewCertificates0194.C6225, NewCertificates0194.C6226, NewCertificates0194.C6227}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1379599742707212480).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1379599742707212480 D i ∧ offSum 1379599742707212480 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1379599742707212480 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1379599742707212480 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1379599742707212480 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1379599742707212480 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport130
