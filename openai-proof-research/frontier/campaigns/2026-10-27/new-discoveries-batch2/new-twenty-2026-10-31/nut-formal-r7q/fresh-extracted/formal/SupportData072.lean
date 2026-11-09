import SignedCatalogue
import NewCertificates0108
import NewCertificates0109
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport072
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 2, 6, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0108.C3462, NewCertificates0108.C3463, NewCertificates0108.C3464, NewCertificates0108.C3465, NewCertificates0108.C3466, NewCertificates0108.C3467, NewCertificates0108.C3468, NewCertificates0108.C3469, NewCertificates0108.C3470, NewCertificates0108.C3471, NewCertificates0108.C3472, NewCertificates0108.C3473, NewCertificates0108.C3474, NewCertificates0108.C3475, NewCertificates0108.C3476, NewCertificates0108.C3477, NewCertificates0108.C3478, NewCertificates0108.C3479, NewCertificates0108.C3480, NewCertificates0108.C3481, NewCertificates0108.C3482, NewCertificates0108.C3483, NewCertificates0108.C3484, NewCertificates0108.C3485, NewCertificates0108.C3486, NewCertificates0108.C3487, NewCertificates0109.C3488, NewCertificates0109.C3489, NewCertificates0109.C3490, NewCertificates0109.C3491, NewCertificates0109.C3492, NewCertificates0109.C3493}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2530044735819653248).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2530044735819653248 D i ∧ offSum 2530044735819653248 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2530044735819653248 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2530044735819653248 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2530044735819653248 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2530044735819653248 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport072
