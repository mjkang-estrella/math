import SignedCatalogue
import NewCertificates0114
import NewCertificates0115
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport077
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 5, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0114.C3654, NewCertificates0114.C3655, NewCertificates0114.C3656, NewCertificates0114.C3657, NewCertificates0114.C3658, NewCertificates0114.C3659, NewCertificates0114.C3660, NewCertificates0114.C3661, NewCertificates0114.C3662, NewCertificates0114.C3663, NewCertificates0114.C3664, NewCertificates0114.C3665, NewCertificates0114.C3666, NewCertificates0114.C3667, NewCertificates0114.C3668, NewCertificates0114.C3669, NewCertificates0114.C3670, NewCertificates0114.C3671, NewCertificates0114.C3672, NewCertificates0114.C3673, NewCertificates0114.C3674, NewCertificates0114.C3675, NewCertificates0114.C3676, NewCertificates0114.C3677, NewCertificates0114.C3678, NewCertificates0114.C3679, NewCertificates0115.C3680, NewCertificates0115.C3681, NewCertificates0115.C3682, NewCertificates0115.C3683, NewCertificates0115.C3684, NewCertificates0115.C3685}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1805409796062470272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1805409796062470272 D i ∧ offSum 1805409796062470272 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1805409796062470272 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1805409796062470272 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1805409796062470272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport077
