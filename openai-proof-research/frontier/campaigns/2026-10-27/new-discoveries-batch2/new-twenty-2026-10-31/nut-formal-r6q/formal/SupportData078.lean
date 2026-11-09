import SignedCatalogue
import NewCertificates0115
import NewCertificates0116
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport078
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 1, 3, 2, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0115.C3686, NewCertificates0115.C3687, NewCertificates0115.C3688, NewCertificates0115.C3689, NewCertificates0115.C3690, NewCertificates0115.C3691, NewCertificates0115.C3692, NewCertificates0115.C3693, NewCertificates0115.C3694, NewCertificates0115.C3695, NewCertificates0115.C3696, NewCertificates0115.C3697, NewCertificates0115.C3698, NewCertificates0115.C3699, NewCertificates0115.C3700, NewCertificates0115.C3701, NewCertificates0115.C3702, NewCertificates0115.C3703, NewCertificates0115.C3704, NewCertificates0115.C3705, NewCertificates0115.C3706, NewCertificates0115.C3707, NewCertificates0115.C3708, NewCertificates0115.C3709, NewCertificates0115.C3710, NewCertificates0115.C3711, NewCertificates0116.C3712, NewCertificates0116.C3713, NewCertificates0116.C3714, NewCertificates0116.C3715, NewCertificates0116.C3716, NewCertificates0116.C3717, NewCertificates0116.C3718, NewCertificates0116.C3719, NewCertificates0116.C3720, NewCertificates0116.C3721, NewCertificates0116.C3722, NewCertificates0116.C3723, NewCertificates0116.C3724, NewCertificates0116.C3725, NewCertificates0116.C3726, NewCertificates0116.C3727, NewCertificates0116.C3728, NewCertificates0116.C3729, NewCertificates0116.C3730, NewCertificates0116.C3731, NewCertificates0116.C3732, NewCertificates0116.C3733}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 7027456053513052288).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7027456053513052288 D i ∧ offSum 7027456053513052288 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 7027456053513052288 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7027456053513052288 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7027456053513052288 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7027456053513052288 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7027456053513052288 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport078
