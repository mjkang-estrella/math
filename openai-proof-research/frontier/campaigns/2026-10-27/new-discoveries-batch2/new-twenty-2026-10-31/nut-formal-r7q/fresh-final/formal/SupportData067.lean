import SignedCatalogue
import NewCertificates0097
import NewCertificates0098
import NewCertificates0099
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport067
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 6, 3, 4, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0097.C3110, NewCertificates0097.C3111, NewCertificates0097.C3112, NewCertificates0097.C3113, NewCertificates0097.C3114, NewCertificates0097.C3115, NewCertificates0097.C3116, NewCertificates0097.C3117, NewCertificates0097.C3118, NewCertificates0097.C3119, NewCertificates0097.C3120, NewCertificates0097.C3121, NewCertificates0097.C3122, NewCertificates0097.C3123, NewCertificates0097.C3124, NewCertificates0097.C3125, NewCertificates0097.C3126, NewCertificates0097.C3127, NewCertificates0097.C3128, NewCertificates0097.C3129, NewCertificates0097.C3130, NewCertificates0097.C3131, NewCertificates0097.C3132, NewCertificates0097.C3133, NewCertificates0097.C3134, NewCertificates0097.C3135, NewCertificates0098.C3136, NewCertificates0098.C3137, NewCertificates0098.C3138, NewCertificates0098.C3139, NewCertificates0098.C3140, NewCertificates0098.C3141, NewCertificates0098.C3142, NewCertificates0098.C3143, NewCertificates0098.C3144, NewCertificates0098.C3145, NewCertificates0098.C3146, NewCertificates0098.C3147, NewCertificates0098.C3148, NewCertificates0098.C3149, NewCertificates0098.C3150, NewCertificates0098.C3151, NewCertificates0098.C3152, NewCertificates0098.C3153, NewCertificates0098.C3154, NewCertificates0098.C3155, NewCertificates0098.C3156, NewCertificates0098.C3157, NewCertificates0098.C3158, NewCertificates0098.C3159, NewCertificates0098.C3160, NewCertificates0098.C3161, NewCertificates0098.C3162, NewCertificates0098.C3163, NewCertificates0098.C3164, NewCertificates0098.C3165, NewCertificates0098.C3166, NewCertificates0098.C3167, NewCertificates0099.C3168, NewCertificates0099.C3169, NewCertificates0099.C3170, NewCertificates0099.C3171, NewCertificates0099.C3172, NewCertificates0099.C3173}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 5011400449719279744).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5011400449719279744 D i ∧ offSum 5011400449719279744 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 5011400449719279744 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5011400449719279744 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5011400449719279744 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5011400449719279744 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5011400449719279744 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5011400449719279744 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5011400449719279744 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport067
