import SignedCatalogue
import NewCertificates0118
import NewCertificates0119
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport081
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 2, 3, 1, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0118.C3798, NewCertificates0118.C3799, NewCertificates0118.C3800, NewCertificates0118.C3801, NewCertificates0118.C3802, NewCertificates0118.C3803, NewCertificates0118.C3804, NewCertificates0118.C3805, NewCertificates0118.C3806, NewCertificates0118.C3807, NewCertificates0119.C3808, NewCertificates0119.C3809, NewCertificates0119.C3810, NewCertificates0119.C3811, NewCertificates0119.C3812, NewCertificates0119.C3813, NewCertificates0119.C3814, NewCertificates0119.C3815, NewCertificates0119.C3816, NewCertificates0119.C3817, NewCertificates0119.C3818, NewCertificates0119.C3819, NewCertificates0119.C3820, NewCertificates0119.C3821, NewCertificates0119.C3822, NewCertificates0119.C3823, NewCertificates0119.C3824, NewCertificates0119.C3825, NewCertificates0119.C3826, NewCertificates0119.C3827, NewCertificates0119.C3828, NewCertificates0119.C3829}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 3534915093316788352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3534915093316788352 D i ∧ offSum 3534915093316788352 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 3534915093316788352 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3534915093316788352 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3534915093316788352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport081
