import SignedCatalogue
import NewCertificates0194
import NewCertificates0195
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport131
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 1, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0194.C6228, NewCertificates0194.C6229, NewCertificates0194.C6230, NewCertificates0194.C6231, NewCertificates0194.C6232, NewCertificates0194.C6233, NewCertificates0194.C6234, NewCertificates0194.C6235, NewCertificates0194.C6236, NewCertificates0194.C6237, NewCertificates0194.C6238, NewCertificates0194.C6239, NewCertificates0195.C6240, NewCertificates0195.C6241, NewCertificates0195.C6242, NewCertificates0195.C6243, NewCertificates0195.C6244, NewCertificates0195.C6245, NewCertificates0195.C6246, NewCertificates0195.C6247, NewCertificates0195.C6248, NewCertificates0195.C6249, NewCertificates0195.C6250, NewCertificates0195.C6251, NewCertificates0195.C6252, NewCertificates0195.C6253, NewCertificates0195.C6254, NewCertificates0195.C6255, NewCertificates0195.C6256, NewCertificates0195.C6257, NewCertificates0195.C6258, NewCertificates0195.C6259}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 2528087741552959680).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2528087741552959680 D i ∧ offSum 2528087741552959680 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2528087741552959680 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2528087741552959680 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2528087741552959680 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2528087741552959680 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport131
