import SignedCatalogue
import NewCertificates0229
import NewCertificates0230
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport155
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 4, 6, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0229.C7336, NewCertificates0229.C7337, NewCertificates0229.C7338, NewCertificates0229.C7339, NewCertificates0229.C7340, NewCertificates0229.C7341, NewCertificates0229.C7342, NewCertificates0229.C7343, NewCertificates0229.C7344, NewCertificates0229.C7345, NewCertificates0229.C7346, NewCertificates0229.C7347, NewCertificates0229.C7348, NewCertificates0229.C7349, NewCertificates0229.C7350, NewCertificates0229.C7351, NewCertificates0229.C7352, NewCertificates0229.C7353, NewCertificates0229.C7354, NewCertificates0229.C7355, NewCertificates0229.C7356, NewCertificates0229.C7357, NewCertificates0229.C7358, NewCertificates0229.C7359, NewCertificates0230.C7360, NewCertificates0230.C7361, NewCertificates0230.C7362, NewCertificates0230.C7363, NewCertificates0230.C7364, NewCertificates0230.C7365, NewCertificates0230.C7366, NewCertificates0230.C7367}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1381568943068057760).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1381568943068057760 D i ∧ offSum 1381568943068057760 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1381568943068057760 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1381568943068057760 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1381568943068057760 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1381568943068057760 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport155
