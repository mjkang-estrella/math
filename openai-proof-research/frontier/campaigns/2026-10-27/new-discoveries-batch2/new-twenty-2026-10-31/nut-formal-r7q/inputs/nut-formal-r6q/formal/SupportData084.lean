import SignedCatalogue
import NewCertificates0121
import NewCertificates0122
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport084
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 5, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0121.C3894, NewCertificates0121.C3895, NewCertificates0121.C3896, NewCertificates0121.C3897, NewCertificates0121.C3898, NewCertificates0121.C3899, NewCertificates0121.C3900, NewCertificates0121.C3901, NewCertificates0121.C3902, NewCertificates0121.C3903, NewCertificates0122.C3904, NewCertificates0122.C3905, NewCertificates0122.C3906, NewCertificates0122.C3907, NewCertificates0122.C3908, NewCertificates0122.C3909, NewCertificates0122.C3910, NewCertificates0122.C3911, NewCertificates0122.C3912, NewCertificates0122.C3913, NewCertificates0122.C3914, NewCertificates0122.C3915, NewCertificates0122.C3916, NewCertificates0122.C3917, NewCertificates0122.C3918, NewCertificates0122.C3919, NewCertificates0122.C3920, NewCertificates0122.C3921, NewCertificates0122.C3922, NewCertificates0122.C3923, NewCertificates0122.C3924, NewCertificates0122.C3925}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 511750526146764928).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 511750526146764928 D i ∧ offSum 511750526146764928 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 511750526146764928 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 511750526146764928 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 511750526146764928 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport084
