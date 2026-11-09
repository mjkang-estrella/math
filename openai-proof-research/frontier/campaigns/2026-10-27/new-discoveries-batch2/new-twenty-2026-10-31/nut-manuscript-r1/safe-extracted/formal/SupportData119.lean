import SignedCatalogue
import NewCertificates0177
import NewCertificates0178
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport119
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 4, 1, 2, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0177.C5676, NewCertificates0177.C5677, NewCertificates0177.C5678, NewCertificates0177.C5679, NewCertificates0177.C5680, NewCertificates0177.C5681, NewCertificates0177.C5682, NewCertificates0177.C5683, NewCertificates0177.C5684, NewCertificates0177.C5685, NewCertificates0177.C5686, NewCertificates0177.C5687, NewCertificates0177.C5688, NewCertificates0177.C5689, NewCertificates0177.C5690, NewCertificates0177.C5691, NewCertificates0177.C5692, NewCertificates0177.C5693, NewCertificates0177.C5694, NewCertificates0177.C5695, NewCertificates0178.C5696, NewCertificates0178.C5697, NewCertificates0178.C5698, NewCertificates0178.C5699, NewCertificates0178.C5700, NewCertificates0178.C5701, NewCertificates0178.C5702, NewCertificates0178.C5703, NewCertificates0178.C5704, NewCertificates0178.C5705, NewCertificates0178.C5706, NewCertificates0178.C5707, NewCertificates0178.C5708, NewCertificates0178.C5709, NewCertificates0178.C5710, NewCertificates0178.C5711, NewCertificates0178.C5712, NewCertificates0178.C5713, NewCertificates0178.C5714, NewCertificates0178.C5715, NewCertificates0178.C5716, NewCertificates0178.C5717, NewCertificates0178.C5718, NewCertificates0178.C5719, NewCertificates0178.C5720, NewCertificates0178.C5721, NewCertificates0178.C5722, NewCertificates0178.C5723}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 511446940343378112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 511446940343378112 D i ∧ offSum 511446940343378112 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 511446940343378112 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 511446940343378112 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 511446940343378112 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 511446940343378112 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 511446940343378112 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 511446940343378112 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 511446940343378112 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 511446940343378112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport119
