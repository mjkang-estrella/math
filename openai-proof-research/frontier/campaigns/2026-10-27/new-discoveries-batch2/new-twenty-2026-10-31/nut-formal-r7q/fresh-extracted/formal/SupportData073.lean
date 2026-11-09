import SignedCatalogue
import NewCertificates0109
import NewCertificates0110
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport073
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 6, 2, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0109.C3494, NewCertificates0109.C3495, NewCertificates0109.C3496, NewCertificates0109.C3497, NewCertificates0109.C3498, NewCertificates0109.C3499, NewCertificates0109.C3500, NewCertificates0109.C3501, NewCertificates0109.C3502, NewCertificates0109.C3503, NewCertificates0109.C3504, NewCertificates0109.C3505, NewCertificates0109.C3506, NewCertificates0109.C3507, NewCertificates0109.C3508, NewCertificates0109.C3509, NewCertificates0109.C3510, NewCertificates0109.C3511, NewCertificates0109.C3512, NewCertificates0109.C3513, NewCertificates0109.C3514, NewCertificates0109.C3515, NewCertificates0109.C3516, NewCertificates0109.C3517, NewCertificates0109.C3518, NewCertificates0109.C3519, NewCertificates0110.C3520, NewCertificates0110.C3521, NewCertificates0110.C3522, NewCertificates0110.C3523, NewCertificates0110.C3524, NewCertificates0110.C3525, NewCertificates0110.C3526, NewCertificates0110.C3527, NewCertificates0110.C3528, NewCertificates0110.C3529, NewCertificates0110.C3530, NewCertificates0110.C3531, NewCertificates0110.C3532, NewCertificates0110.C3533, NewCertificates0110.C3534, NewCertificates0110.C3535, NewCertificates0110.C3536, NewCertificates0110.C3537, NewCertificates0110.C3538, NewCertificates0110.C3539, NewCertificates0110.C3540, NewCertificates0110.C3541}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
theorem doubled_enumeration : ((supportEdges 2534614048445603968).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2534614048445603968 D i ∧ offSum 2534614048445603968 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 2534614048445603968 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2534614048445603968 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2534614048445603968 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2534614048445603968 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2534614048445603968 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport073
