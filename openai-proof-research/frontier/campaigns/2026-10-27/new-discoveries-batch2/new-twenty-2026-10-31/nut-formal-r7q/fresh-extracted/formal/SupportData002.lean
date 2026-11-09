import SignedCatalogue
import NewCertificates0002
import NewCertificates0003
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport002
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 6, 2, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0002.C80, NewCertificates0002.C81, NewCertificates0002.C82, NewCertificates0002.C83, NewCertificates0002.C84, NewCertificates0002.C85, NewCertificates0002.C86, NewCertificates0002.C87, NewCertificates0002.C88, NewCertificates0002.C89, NewCertificates0002.C90, NewCertificates0002.C91, NewCertificates0002.C92, NewCertificates0002.C93, NewCertificates0002.C94, NewCertificates0002.C95, NewCertificates0003.C96, NewCertificates0003.C97, NewCertificates0003.C98, NewCertificates0003.C99, NewCertificates0003.C100, NewCertificates0003.C101, NewCertificates0003.C102, NewCertificates0003.C103, NewCertificates0003.C104, NewCertificates0003.C105, NewCertificates0003.C106, NewCertificates0003.C107, NewCertificates0003.C108, NewCertificates0003.C109, NewCertificates0003.C110, NewCertificates0003.C111, NewCertificates0003.C112, NewCertificates0003.C113, NewCertificates0003.C114, NewCertificates0003.C115, NewCertificates0003.C116, NewCertificates0003.C117, NewCertificates0003.C118, NewCertificates0003.C119, NewCertificates0003.C120, NewCertificates0003.C121, NewCertificates0003.C122, NewCertificates0003.C123, NewCertificates0003.C124, NewCertificates0003.C125, NewCertificates0003.C126, NewCertificates0003.C127}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,5)}
theorem doubled_enumeration : ((supportEdges 1383810975521603712).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1383810975521603712 D i ∧ offSum 1383810975521603712 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1383810975521603712 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1383810975521603712 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1383810975521603712 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1383810975521603712 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport002
