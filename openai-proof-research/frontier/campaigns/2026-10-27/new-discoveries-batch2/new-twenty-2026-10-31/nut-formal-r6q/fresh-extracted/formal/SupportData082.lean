import SignedCatalogue
import NewCertificates0119
import NewCertificates0120
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport082
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 2, 6, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0119.C3830, NewCertificates0119.C3831, NewCertificates0119.C3832, NewCertificates0119.C3833, NewCertificates0119.C3834, NewCertificates0119.C3835, NewCertificates0119.C3836, NewCertificates0119.C3837, NewCertificates0119.C3838, NewCertificates0119.C3839, NewCertificates0120.C3840, NewCertificates0120.C3841, NewCertificates0120.C3842, NewCertificates0120.C3843, NewCertificates0120.C3844, NewCertificates0120.C3845, NewCertificates0120.C3846, NewCertificates0120.C3847, NewCertificates0120.C3848, NewCertificates0120.C3849, NewCertificates0120.C3850, NewCertificates0120.C3851, NewCertificates0120.C3852, NewCertificates0120.C3853, NewCertificates0120.C3854, NewCertificates0120.C3855, NewCertificates0120.C3856, NewCertificates0120.C3857, NewCertificates0120.C3858, NewCertificates0120.C3859, NewCertificates0120.C3860, NewCertificates0120.C3861}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1813352667588092032).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1813352667588092032 D i ∧ offSum 1813352667588092032 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1813352667588092032 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1813352667588092032 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1813352667588092032 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport082
