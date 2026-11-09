import SignedCatalogue
import NewCertificates0285
import NewCertificates0286
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport193
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 6, 2, 3, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0285.C9124, NewCertificates0285.C9125, NewCertificates0285.C9126, NewCertificates0285.C9127, NewCertificates0285.C9128, NewCertificates0285.C9129, NewCertificates0285.C9130, NewCertificates0285.C9131, NewCertificates0285.C9132, NewCertificates0285.C9133, NewCertificates0285.C9134, NewCertificates0285.C9135, NewCertificates0285.C9136, NewCertificates0285.C9137, NewCertificates0285.C9138, NewCertificates0285.C9139, NewCertificates0285.C9140, NewCertificates0285.C9141, NewCertificates0285.C9142, NewCertificates0285.C9143, NewCertificates0285.C9144, NewCertificates0285.C9145, NewCertificates0285.C9146, NewCertificates0285.C9147, NewCertificates0285.C9148, NewCertificates0285.C9149, NewCertificates0285.C9150, NewCertificates0285.C9151, NewCertificates0286.C9152, NewCertificates0286.C9153, NewCertificates0286.C9154, NewCertificates0286.C9155, NewCertificates0286.C9156, NewCertificates0286.C9157, NewCertificates0286.C9158, NewCertificates0286.C9159, NewCertificates0286.C9160, NewCertificates0286.C9161, NewCertificates0286.C9162, NewCertificates0286.C9163, NewCertificates0286.C9164, NewCertificates0286.C9165, NewCertificates0286.C9166, NewCertificates0286.C9167, NewCertificates0286.C9168, NewCertificates0286.C9169, NewCertificates0286.C9170, NewCertificates0286.C9171}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,1)}
theorem doubled_enumeration : ((supportEdges 950915279475982722).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950915279475982722 D i ∧ offSum 950915279475982722 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 950915279475982722 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 950915279475982722 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950915279475982722 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950915279475982722 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport193
