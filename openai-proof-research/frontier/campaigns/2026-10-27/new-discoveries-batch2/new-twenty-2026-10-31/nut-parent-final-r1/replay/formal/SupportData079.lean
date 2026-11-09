import SignedCatalogue
import NewCertificates0116
import NewCertificates0117
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport079
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 5, 2, 1, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0116.C3734, NewCertificates0116.C3735, NewCertificates0116.C3736, NewCertificates0116.C3737, NewCertificates0116.C3738, NewCertificates0116.C3739, NewCertificates0116.C3740, NewCertificates0116.C3741, NewCertificates0116.C3742, NewCertificates0116.C3743, NewCertificates0117.C3744, NewCertificates0117.C3745, NewCertificates0117.C3746, NewCertificates0117.C3747, NewCertificates0117.C3748, NewCertificates0117.C3749, NewCertificates0117.C3750, NewCertificates0117.C3751, NewCertificates0117.C3752, NewCertificates0117.C3753, NewCertificates0117.C3754, NewCertificates0117.C3755, NewCertificates0117.C3756, NewCertificates0117.C3757, NewCertificates0117.C3758, NewCertificates0117.C3759, NewCertificates0117.C3760, NewCertificates0117.C3761, NewCertificates0117.C3762, NewCertificates0117.C3763, NewCertificates0117.C3764, NewCertificates0117.C3765}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1812217868177137792).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1812217868177137792 D i ∧ offSum 1812217868177137792 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1812217868177137792 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1812217868177137792 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1812217868177137792 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport079
