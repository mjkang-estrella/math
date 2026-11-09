import SignedCatalogue
import NewCertificates0006
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport004
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 5, 6, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0006.C192, NewCertificates0006.C193, NewCertificates0006.C194, NewCertificates0006.C195, NewCertificates0006.C196, NewCertificates0006.C197, NewCertificates0006.C198, NewCertificates0006.C199, NewCertificates0006.C200, NewCertificates0006.C201, NewCertificates0006.C202, NewCertificates0006.C203, NewCertificates0006.C204, NewCertificates0006.C205, NewCertificates0006.C206, NewCertificates0006.C207, NewCertificates0006.C208, NewCertificates0006.C209, NewCertificates0006.C210, NewCertificates0006.C211, NewCertificates0006.C212, NewCertificates0006.C213, NewCertificates0006.C214, NewCertificates0006.C215, NewCertificates0006.C216, NewCertificates0006.C217, NewCertificates0006.C218, NewCertificates0006.C219, NewCertificates0006.C220, NewCertificates0006.C221, NewCertificates0006.C222, NewCertificates0006.C223}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1383828705146601600).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1383828705146601600 D i ∧ offSum 1383828705146601600 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1383828705146601600 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1383828705146601600 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1383828705146601600 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport004
