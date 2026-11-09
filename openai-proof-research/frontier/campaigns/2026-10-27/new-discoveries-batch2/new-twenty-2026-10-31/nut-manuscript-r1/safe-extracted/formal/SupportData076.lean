import SignedCatalogue
import NewCertificates0112
import NewCertificates0113
import NewCertificates0114
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport076
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 5, 4, 1, 6, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0112.C3606, NewCertificates0112.C3607, NewCertificates0112.C3608, NewCertificates0112.C3609, NewCertificates0112.C3610, NewCertificates0112.C3611, NewCertificates0112.C3612, NewCertificates0112.C3613, NewCertificates0112.C3614, NewCertificates0112.C3615, NewCertificates0113.C3616, NewCertificates0113.C3617, NewCertificates0113.C3618, NewCertificates0113.C3619, NewCertificates0113.C3620, NewCertificates0113.C3621, NewCertificates0113.C3622, NewCertificates0113.C3623, NewCertificates0113.C3624, NewCertificates0113.C3625, NewCertificates0113.C3626, NewCertificates0113.C3627, NewCertificates0113.C3628, NewCertificates0113.C3629, NewCertificates0113.C3630, NewCertificates0113.C3631, NewCertificates0113.C3632, NewCertificates0113.C3633, NewCertificates0113.C3634, NewCertificates0113.C3635, NewCertificates0113.C3636, NewCertificates0113.C3637, NewCertificates0113.C3638, NewCertificates0113.C3639, NewCertificates0113.C3640, NewCertificates0113.C3641, NewCertificates0113.C3642, NewCertificates0113.C3643, NewCertificates0113.C3644, NewCertificates0113.C3645, NewCertificates0113.C3646, NewCertificates0113.C3647, NewCertificates0114.C3648, NewCertificates0114.C3649, NewCertificates0114.C3650, NewCertificates0114.C3651, NewCertificates0114.C3652, NewCertificates0114.C3653}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 2678166286572216448).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2678166286572216448 D i ∧ offSum 2678166286572216448 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 2678166286572216448 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2678166286572216448 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2678166286572216448 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2678166286572216448 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2678166286572216448 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport076
