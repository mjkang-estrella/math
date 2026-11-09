import SignedCatalogue
import NewCertificates0004
import NewCertificates0005
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport003
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 6, 2, 4, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0004.C128, NewCertificates0004.C129, NewCertificates0004.C130, NewCertificates0004.C131, NewCertificates0004.C132, NewCertificates0004.C133, NewCertificates0004.C134, NewCertificates0004.C135, NewCertificates0004.C136, NewCertificates0004.C137, NewCertificates0004.C138, NewCertificates0004.C139, NewCertificates0004.C140, NewCertificates0004.C141, NewCertificates0004.C142, NewCertificates0004.C143, NewCertificates0004.C144, NewCertificates0004.C145, NewCertificates0004.C146, NewCertificates0004.C147, NewCertificates0004.C148, NewCertificates0004.C149, NewCertificates0004.C150, NewCertificates0004.C151, NewCertificates0004.C152, NewCertificates0004.C153, NewCertificates0004.C154, NewCertificates0004.C155, NewCertificates0004.C156, NewCertificates0004.C157, NewCertificates0004.C158, NewCertificates0004.C159, NewCertificates0005.C160, NewCertificates0005.C161, NewCertificates0005.C162, NewCertificates0005.C163, NewCertificates0005.C164, NewCertificates0005.C165, NewCertificates0005.C166, NewCertificates0005.C167, NewCertificates0005.C168, NewCertificates0005.C169, NewCertificates0005.C170, NewCertificates0005.C171, NewCertificates0005.C172, NewCertificates0005.C173, NewCertificates0005.C174, NewCertificates0005.C175, NewCertificates0005.C176, NewCertificates0005.C177, NewCertificates0005.C178, NewCertificates0005.C179, NewCertificates0005.C180, NewCertificates0005.C181, NewCertificates0005.C182, NewCertificates0005.C183, NewCertificates0005.C184, NewCertificates0005.C185, NewCertificates0005.C186, NewCertificates0005.C187, NewCertificates0005.C188, NewCertificates0005.C189, NewCertificates0005.C190, NewCertificates0005.C191}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,5)}
theorem doubled_enumeration : ((supportEdges 4869543898231373952).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4869543898231373952 D i ∧ offSum 4869543898231373952 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 4869543898231373952 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4869543898231373952 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4869543898231373952 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4869543898231373952 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4869543898231373952 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport003
