import SignedCatalogue
import NewCertificates0099
import NewCertificates0100
import NewCertificates0101
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport068
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 5, 3, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0099.C3174, NewCertificates0099.C3175, NewCertificates0099.C3176, NewCertificates0099.C3177, NewCertificates0099.C3178, NewCertificates0099.C3179, NewCertificates0099.C3180, NewCertificates0099.C3181, NewCertificates0099.C3182, NewCertificates0099.C3183, NewCertificates0099.C3184, NewCertificates0099.C3185, NewCertificates0099.C3186, NewCertificates0099.C3187, NewCertificates0099.C3188, NewCertificates0099.C3189, NewCertificates0099.C3190, NewCertificates0099.C3191, NewCertificates0099.C3192, NewCertificates0099.C3193, NewCertificates0099.C3194, NewCertificates0099.C3195, NewCertificates0099.C3196, NewCertificates0099.C3197, NewCertificates0099.C3198, NewCertificates0099.C3199, NewCertificates0100.C3200, NewCertificates0100.C3201, NewCertificates0100.C3202, NewCertificates0100.C3203, NewCertificates0100.C3204, NewCertificates0100.C3205, NewCertificates0100.C3206, NewCertificates0100.C3207, NewCertificates0100.C3208, NewCertificates0100.C3209, NewCertificates0100.C3210, NewCertificates0100.C3211, NewCertificates0100.C3212, NewCertificates0100.C3213, NewCertificates0100.C3214, NewCertificates0100.C3215, NewCertificates0100.C3216, NewCertificates0100.C3217, NewCertificates0100.C3218, NewCertificates0100.C3219, NewCertificates0100.C3220, NewCertificates0100.C3221, NewCertificates0100.C3222, NewCertificates0100.C3223, NewCertificates0100.C3224, NewCertificates0100.C3225, NewCertificates0100.C3226, NewCertificates0100.C3227, NewCertificates0100.C3228, NewCertificates0100.C3229, NewCertificates0100.C3230, NewCertificates0100.C3231, NewCertificates0101.C3232, NewCertificates0101.C3233, NewCertificates0101.C3234, NewCertificates0101.C3235, NewCertificates0101.C3236, NewCertificates0101.C3237, NewCertificates0101.C3238, NewCertificates0101.C3239, NewCertificates0101.C3240, NewCertificates0101.C3241, NewCertificates0101.C3242, NewCertificates0101.C3243, NewCertificates0101.C3244, NewCertificates0101.C3245}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 5014765092737130624).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5014765092737130624 D i ∧ offSum 5014765092737130624 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 5014765092737130624 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5014765092737130624 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5014765092737130624 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5014765092737130624 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5014765092737130624 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5014765092737130624 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5014765092737130624 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5014765092737130624 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport068
