import SignedCatalogue
import NewCertificates0110
import NewCertificates0111
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport074
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 5, 4, 1, 2, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0110.C3542, NewCertificates0110.C3543, NewCertificates0110.C3544, NewCertificates0110.C3545, NewCertificates0110.C3546, NewCertificates0110.C3547, NewCertificates0110.C3548, NewCertificates0110.C3549, NewCertificates0110.C3550, NewCertificates0110.C3551, NewCertificates0111.C3552, NewCertificates0111.C3553, NewCertificates0111.C3554, NewCertificates0111.C3555, NewCertificates0111.C3556, NewCertificates0111.C3557, NewCertificates0111.C3558, NewCertificates0111.C3559, NewCertificates0111.C3560, NewCertificates0111.C3561, NewCertificates0111.C3562, NewCertificates0111.C3563, NewCertificates0111.C3564, NewCertificates0111.C3565, NewCertificates0111.C3566, NewCertificates0111.C3567, NewCertificates0111.C3568, NewCertificates0111.C3569, NewCertificates0111.C3570, NewCertificates0111.C3571, NewCertificates0111.C3572, NewCertificates0111.C3573}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2960701451260682368).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2960701451260682368 D i ∧ offSum 2960701451260682368 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2960701451260682368 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2960701451260682368 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2960701451260682368 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2960701451260682368 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport074
