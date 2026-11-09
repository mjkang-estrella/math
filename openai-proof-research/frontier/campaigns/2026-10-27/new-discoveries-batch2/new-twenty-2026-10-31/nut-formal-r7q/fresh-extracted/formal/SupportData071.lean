import SignedCatalogue
import NewCertificates0105
import NewCertificates0106
import NewCertificates0107
import NewCertificates0108
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport071
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 1, 2, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0105.C3390, NewCertificates0105.C3391, NewCertificates0106.C3392, NewCertificates0106.C3393, NewCertificates0106.C3394, NewCertificates0106.C3395, NewCertificates0106.C3396, NewCertificates0106.C3397, NewCertificates0106.C3398, NewCertificates0106.C3399, NewCertificates0106.C3400, NewCertificates0106.C3401, NewCertificates0106.C3402, NewCertificates0106.C3403, NewCertificates0106.C3404, NewCertificates0106.C3405, NewCertificates0106.C3406, NewCertificates0106.C3407, NewCertificates0106.C3408, NewCertificates0106.C3409, NewCertificates0106.C3410, NewCertificates0106.C3411, NewCertificates0106.C3412, NewCertificates0106.C3413, NewCertificates0106.C3414, NewCertificates0106.C3415, NewCertificates0106.C3416, NewCertificates0106.C3417, NewCertificates0106.C3418, NewCertificates0106.C3419, NewCertificates0106.C3420, NewCertificates0106.C3421, NewCertificates0106.C3422, NewCertificates0106.C3423, NewCertificates0107.C3424, NewCertificates0107.C3425, NewCertificates0107.C3426, NewCertificates0107.C3427, NewCertificates0107.C3428, NewCertificates0107.C3429, NewCertificates0107.C3430, NewCertificates0107.C3431, NewCertificates0107.C3432, NewCertificates0107.C3433, NewCertificates0107.C3434, NewCertificates0107.C3435, NewCertificates0107.C3436, NewCertificates0107.C3437, NewCertificates0107.C3438, NewCertificates0107.C3439, NewCertificates0107.C3440, NewCertificates0107.C3441, NewCertificates0107.C3442, NewCertificates0107.C3443, NewCertificates0107.C3444, NewCertificates0107.C3445, NewCertificates0107.C3446, NewCertificates0107.C3447, NewCertificates0107.C3448, NewCertificates0107.C3449, NewCertificates0107.C3450, NewCertificates0107.C3451, NewCertificates0107.C3452, NewCertificates0107.C3453, NewCertificates0107.C3454, NewCertificates0107.C3455, NewCertificates0108.C3456, NewCertificates0108.C3457, NewCertificates0108.C3458, NewCertificates0108.C3459, NewCertificates0108.C3460, NewCertificates0108.C3461}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 7029136107817148544).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7029136107817148544 D i ∧ offSum 7029136107817148544 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 7029136107817148544 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7029136107817148544 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7029136107817148544 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7029136107817148544 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 7029136107817148544 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 7029136107817148544 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7029136107817148544 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7029136107817148544 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport071
