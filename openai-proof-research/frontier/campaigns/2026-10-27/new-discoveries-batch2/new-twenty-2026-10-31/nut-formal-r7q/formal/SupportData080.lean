import SignedCatalogue
import NewCertificates0117
import NewCertificates0118
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport080
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 6, 4, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0117.C3766, NewCertificates0117.C3767, NewCertificates0117.C3768, NewCertificates0117.C3769, NewCertificates0117.C3770, NewCertificates0117.C3771, NewCertificates0117.C3772, NewCertificates0117.C3773, NewCertificates0117.C3774, NewCertificates0117.C3775, NewCertificates0118.C3776, NewCertificates0118.C3777, NewCertificates0118.C3778, NewCertificates0118.C3779, NewCertificates0118.C3780, NewCertificates0118.C3781, NewCertificates0118.C3782, NewCertificates0118.C3783, NewCertificates0118.C3784, NewCertificates0118.C3785, NewCertificates0118.C3786, NewCertificates0118.C3787, NewCertificates0118.C3788, NewCertificates0118.C3789, NewCertificates0118.C3790, NewCertificates0118.C3791, NewCertificates0118.C3792, NewCertificates0118.C3793, NewCertificates0118.C3794, NewCertificates0118.C3795, NewCertificates0118.C3796, NewCertificates0118.C3797}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5297950790886908032).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5297950790886908032 D i ∧ offSum 5297950790886908032 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5297950790886908032 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5297950790886908032 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5297950790886908032 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport080
