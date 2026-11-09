import SignedCatalogue
import NewCertificates0094
import NewCertificates0095
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport065
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 6, 4, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0094.C3014, NewCertificates0094.C3015, NewCertificates0094.C3016, NewCertificates0094.C3017, NewCertificates0094.C3018, NewCertificates0094.C3019, NewCertificates0094.C3020, NewCertificates0094.C3021, NewCertificates0094.C3022, NewCertificates0094.C3023, NewCertificates0094.C3024, NewCertificates0094.C3025, NewCertificates0094.C3026, NewCertificates0094.C3027, NewCertificates0094.C3028, NewCertificates0094.C3029, NewCertificates0094.C3030, NewCertificates0094.C3031, NewCertificates0094.C3032, NewCertificates0094.C3033, NewCertificates0094.C3034, NewCertificates0094.C3035, NewCertificates0094.C3036, NewCertificates0094.C3037, NewCertificates0094.C3038, NewCertificates0094.C3039, NewCertificates0095.C3040, NewCertificates0095.C3041, NewCertificates0095.C3042, NewCertificates0095.C3043, NewCertificates0095.C3044, NewCertificates0095.C3045, NewCertificates0095.C3046, NewCertificates0095.C3047, NewCertificates0095.C3048, NewCertificates0095.C3049, NewCertificates0095.C3050, NewCertificates0095.C3051, NewCertificates0095.C3052, NewCertificates0095.C3053, NewCertificates0095.C3054, NewCertificates0095.C3055, NewCertificates0095.C3056, NewCertificates0095.C3057, NewCertificates0095.C3058, NewCertificates0095.C3059, NewCertificates0095.C3060, NewCertificates0095.C3061}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 951458300715606144).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 951458300715606144 D i ∧ offSum 951458300715606144 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 951458300715606144 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 951458300715606144 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 951458300715606144 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 951458300715606144 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 951458300715606144 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 951458300715606144 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport065
