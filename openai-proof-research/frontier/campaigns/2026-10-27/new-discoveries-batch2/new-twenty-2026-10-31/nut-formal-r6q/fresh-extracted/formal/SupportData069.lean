import SignedCatalogue
import NewCertificates0101
import NewCertificates0102
import NewCertificates0103
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport069
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 6, 4, 2, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0101.C3246, NewCertificates0101.C3247, NewCertificates0101.C3248, NewCertificates0101.C3249, NewCertificates0101.C3250, NewCertificates0101.C3251, NewCertificates0101.C3252, NewCertificates0101.C3253, NewCertificates0101.C3254, NewCertificates0101.C3255, NewCertificates0101.C3256, NewCertificates0101.C3257, NewCertificates0101.C3258, NewCertificates0101.C3259, NewCertificates0101.C3260, NewCertificates0101.C3261, NewCertificates0101.C3262, NewCertificates0101.C3263, NewCertificates0102.C3264, NewCertificates0102.C3265, NewCertificates0102.C3266, NewCertificates0102.C3267, NewCertificates0102.C3268, NewCertificates0102.C3269, NewCertificates0102.C3270, NewCertificates0102.C3271, NewCertificates0102.C3272, NewCertificates0102.C3273, NewCertificates0102.C3274, NewCertificates0102.C3275, NewCertificates0102.C3276, NewCertificates0102.C3277, NewCertificates0102.C3278, NewCertificates0102.C3279, NewCertificates0102.C3280, NewCertificates0102.C3281, NewCertificates0102.C3282, NewCertificates0102.C3283, NewCertificates0102.C3284, NewCertificates0102.C3285, NewCertificates0102.C3286, NewCertificates0102.C3287, NewCertificates0102.C3288, NewCertificates0102.C3289, NewCertificates0102.C3290, NewCertificates0102.C3291, NewCertificates0102.C3292, NewCertificates0102.C3293, NewCertificates0102.C3294, NewCertificates0102.C3295, NewCertificates0103.C3296, NewCertificates0103.C3297, NewCertificates0103.C3298, NewCertificates0103.C3299, NewCertificates0103.C3300, NewCertificates0103.C3301, NewCertificates0103.C3302, NewCertificates0103.C3303, NewCertificates0103.C3304, NewCertificates0103.C3305, NewCertificates0103.C3306, NewCertificates0103.C3307, NewCertificates0103.C3308, NewCertificates0103.C3309, NewCertificates0103.C3310, NewCertificates0103.C3311, NewCertificates0103.C3312, NewCertificates0103.C3313, NewCertificates0103.C3314, NewCertificates0103.C3315, NewCertificates0103.C3316, NewCertificates0103.C3317}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 5301869570051547264).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5301869570051547264 D i ∧ offSum 5301869570051547264 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 5301869570051547264 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5301869570051547264 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5301869570051547264 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5301869570051547264 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5301869570051547264 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5301869570051547264 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5301869570051547264 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5301869570051547264 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport069
