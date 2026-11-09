import SignedCatalogue
import NewCertificates0095
import NewCertificates0096
import NewCertificates0097
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport066
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 5, 6, 1, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0095.C3062, NewCertificates0095.C3063, NewCertificates0095.C3064, NewCertificates0095.C3065, NewCertificates0095.C3066, NewCertificates0095.C3067, NewCertificates0095.C3068, NewCertificates0095.C3069, NewCertificates0095.C3070, NewCertificates0095.C3071, NewCertificates0096.C3072, NewCertificates0096.C3073, NewCertificates0096.C3074, NewCertificates0096.C3075, NewCertificates0096.C3076, NewCertificates0096.C3077, NewCertificates0096.C3078, NewCertificates0096.C3079, NewCertificates0096.C3080, NewCertificates0096.C3081, NewCertificates0096.C3082, NewCertificates0096.C3083, NewCertificates0096.C3084, NewCertificates0096.C3085, NewCertificates0096.C3086, NewCertificates0096.C3087, NewCertificates0096.C3088, NewCertificates0096.C3089, NewCertificates0096.C3090, NewCertificates0096.C3091, NewCertificates0096.C3092, NewCertificates0096.C3093, NewCertificates0096.C3094, NewCertificates0096.C3095, NewCertificates0096.C3096, NewCertificates0096.C3097, NewCertificates0096.C3098, NewCertificates0096.C3099, NewCertificates0096.C3100, NewCertificates0096.C3101, NewCertificates0096.C3102, NewCertificates0096.C3103, NewCertificates0097.C3104, NewCertificates0097.C3105, NewCertificates0097.C3106, NewCertificates0097.C3107, NewCertificates0097.C3108, NewCertificates0097.C3109}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 2674155525855256704).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2674155525855256704 D i ∧ offSum 2674155525855256704 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2674155525855256704 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2674155525855256704 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2674155525855256704 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2674155525855256704 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2674155525855256704 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2674155525855256704 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport066
