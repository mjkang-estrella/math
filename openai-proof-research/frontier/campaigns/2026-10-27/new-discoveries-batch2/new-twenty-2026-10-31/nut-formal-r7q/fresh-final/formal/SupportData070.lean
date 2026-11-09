import SignedCatalogue
import NewCertificates0103
import NewCertificates0104
import NewCertificates0105
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport070
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 4, 3, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0103.C3318, NewCertificates0103.C3319, NewCertificates0103.C3320, NewCertificates0103.C3321, NewCertificates0103.C3322, NewCertificates0103.C3323, NewCertificates0103.C3324, NewCertificates0103.C3325, NewCertificates0103.C3326, NewCertificates0103.C3327, NewCertificates0104.C3328, NewCertificates0104.C3329, NewCertificates0104.C3330, NewCertificates0104.C3331, NewCertificates0104.C3332, NewCertificates0104.C3333, NewCertificates0104.C3334, NewCertificates0104.C3335, NewCertificates0104.C3336, NewCertificates0104.C3337, NewCertificates0104.C3338, NewCertificates0104.C3339, NewCertificates0104.C3340, NewCertificates0104.C3341, NewCertificates0104.C3342, NewCertificates0104.C3343, NewCertificates0104.C3344, NewCertificates0104.C3345, NewCertificates0104.C3346, NewCertificates0104.C3347, NewCertificates0104.C3348, NewCertificates0104.C3349, NewCertificates0104.C3350, NewCertificates0104.C3351, NewCertificates0104.C3352, NewCertificates0104.C3353, NewCertificates0104.C3354, NewCertificates0104.C3355, NewCertificates0104.C3356, NewCertificates0104.C3357, NewCertificates0104.C3358, NewCertificates0104.C3359, NewCertificates0105.C3360, NewCertificates0105.C3361, NewCertificates0105.C3362, NewCertificates0105.C3363, NewCertificates0105.C3364, NewCertificates0105.C3365, NewCertificates0105.C3366, NewCertificates0105.C3367, NewCertificates0105.C3368, NewCertificates0105.C3369, NewCertificates0105.C3370, NewCertificates0105.C3371, NewCertificates0105.C3372, NewCertificates0105.C3373, NewCertificates0105.C3374, NewCertificates0105.C3375, NewCertificates0105.C3376, NewCertificates0105.C3377, NewCertificates0105.C3378, NewCertificates0105.C3379, NewCertificates0105.C3380, NewCertificates0105.C3381, NewCertificates0105.C3382, NewCertificates0105.C3383, NewCertificates0105.C3384, NewCertificates0105.C3385, NewCertificates0105.C3386, NewCertificates0105.C3387, NewCertificates0105.C3388, NewCertificates0105.C3389}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 5019334405363081344).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5019334405363081344 D i ∧ offSum 5019334405363081344 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 5019334405363081344 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5019334405363081344 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5019334405363081344 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5019334405363081344 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5019334405363081344 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5019334405363081344 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5019334405363081344 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5019334405363081344 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport070
