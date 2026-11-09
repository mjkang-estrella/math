import SignedCatalogue
import NewCertificates0176
import NewCertificates0177
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport118
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 5, 4, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0176.C5644, NewCertificates0176.C5645, NewCertificates0176.C5646, NewCertificates0176.C5647, NewCertificates0176.C5648, NewCertificates0176.C5649, NewCertificates0176.C5650, NewCertificates0176.C5651, NewCertificates0176.C5652, NewCertificates0176.C5653, NewCertificates0176.C5654, NewCertificates0176.C5655, NewCertificates0176.C5656, NewCertificates0176.C5657, NewCertificates0176.C5658, NewCertificates0176.C5659, NewCertificates0176.C5660, NewCertificates0176.C5661, NewCertificates0176.C5662, NewCertificates0176.C5663, NewCertificates0177.C5664, NewCertificates0177.C5665, NewCertificates0177.C5666, NewCertificates0177.C5667, NewCertificates0177.C5668, NewCertificates0177.C5669, NewCertificates0177.C5670, NewCertificates0177.C5671, NewCertificates0177.C5672, NewCertificates0177.C5673, NewCertificates0177.C5674, NewCertificates0177.C5675}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 1, 1, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 1, 1, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1379038991774957760).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1379038991774957760 D i ∧ offSum 1379038991774957760 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1379038991774957760 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1379038991774957760 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1379038991774957760 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1379038991774957760 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport118
