import SignedCatalogue
import NewCertificates0120
import NewCertificates0121
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport083
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 5, 6, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0120.C3862, NewCertificates0120.C3863, NewCertificates0120.C3864, NewCertificates0120.C3865, NewCertificates0120.C3866, NewCertificates0120.C3867, NewCertificates0120.C3868, NewCertificates0120.C3869, NewCertificates0120.C3870, NewCertificates0120.C3871, NewCertificates0121.C3872, NewCertificates0121.C3873, NewCertificates0121.C3874, NewCertificates0121.C3875, NewCertificates0121.C3876, NewCertificates0121.C3877, NewCertificates0121.C3878, NewCertificates0121.C3879, NewCertificates0121.C3880, NewCertificates0121.C3881, NewCertificates0121.C3882, NewCertificates0121.C3883, NewCertificates0121.C3884, NewCertificates0121.C3885, NewCertificates0121.C3886, NewCertificates0121.C3887, NewCertificates0121.C3888, NewCertificates0121.C3889, NewCertificates0121.C3890, NewCertificates0121.C3891, NewCertificates0121.C3892, NewCertificates0121.C3893}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 508372586113065088).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 508372586113065088 D i ∧ offSum 508372586113065088 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 508372586113065088 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 508372586113065088 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 508372586113065088 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport083
