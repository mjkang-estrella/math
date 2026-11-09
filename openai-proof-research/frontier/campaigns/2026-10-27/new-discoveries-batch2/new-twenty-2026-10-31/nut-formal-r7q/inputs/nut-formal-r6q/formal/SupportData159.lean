import SignedCatalogue
import NewCertificates0234
import NewCertificates0235
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport159
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 4, 2, 1, 6, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0234.C7508, NewCertificates0234.C7509, NewCertificates0234.C7510, NewCertificates0234.C7511, NewCertificates0234.C7512, NewCertificates0234.C7513, NewCertificates0234.C7514, NewCertificates0234.C7515, NewCertificates0234.C7516, NewCertificates0234.C7517, NewCertificates0234.C7518, NewCertificates0234.C7519, NewCertificates0235.C7520, NewCertificates0235.C7521, NewCertificates0235.C7522, NewCertificates0235.C7523, NewCertificates0235.C7524, NewCertificates0235.C7525, NewCertificates0235.C7526, NewCertificates0235.C7527, NewCertificates0235.C7528, NewCertificates0235.C7529, NewCertificates0235.C7530, NewCertificates0235.C7531, NewCertificates0235.C7532, NewCertificates0235.C7533, NewCertificates0235.C7534, NewCertificates0235.C7535, NewCertificates0235.C7536, NewCertificates0235.C7537, NewCertificates0235.C7538, NewCertificates0235.C7539}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 1, 0; 1, 0, 0, 0, 1, 0, 0, 1; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 2673609180040417440).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2673609180040417440 D i ∧ offSum 2673609180040417440 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2673609180040417440 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2673609180040417440 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2673609180040417440 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2673609180040417440 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport159
