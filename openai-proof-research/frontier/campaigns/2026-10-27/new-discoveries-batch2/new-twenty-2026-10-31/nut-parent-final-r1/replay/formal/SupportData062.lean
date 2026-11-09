import SignedCatalogue
import NewCertificates0090
import NewCertificates0091
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport062
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 6, 5, 4, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0090.C2910, NewCertificates0090.C2911, NewCertificates0091.C2912, NewCertificates0091.C2913, NewCertificates0091.C2914, NewCertificates0091.C2915, NewCertificates0091.C2916, NewCertificates0091.C2917, NewCertificates0091.C2918, NewCertificates0091.C2919, NewCertificates0091.C2920, NewCertificates0091.C2921, NewCertificates0091.C2922, NewCertificates0091.C2923, NewCertificates0091.C2924, NewCertificates0091.C2925, NewCertificates0091.C2926, NewCertificates0091.C2927, NewCertificates0091.C2928, NewCertificates0091.C2929, NewCertificates0091.C2930, NewCertificates0091.C2931, NewCertificates0091.C2932, NewCertificates0091.C2933, NewCertificates0091.C2934, NewCertificates0091.C2935, NewCertificates0091.C2936, NewCertificates0091.C2937, NewCertificates0091.C2938, NewCertificates0091.C2939, NewCertificates0091.C2940, NewCertificates0091.C2941}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 799983103395283072).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 799983103395283072 D i ∧ offSum 799983103395283072 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 799983103395283072 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 799983103395283072 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 799983103395283072 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport062
