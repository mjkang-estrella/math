import SignedCatalogue
import NewCertificates0269
import NewCertificates0270
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport183
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 2, 7, 1, 3, 6, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0269.C8620, NewCertificates0269.C8621, NewCertificates0269.C8622, NewCertificates0269.C8623, NewCertificates0269.C8624, NewCertificates0269.C8625, NewCertificates0269.C8626, NewCertificates0269.C8627, NewCertificates0269.C8628, NewCertificates0269.C8629, NewCertificates0269.C8630, NewCertificates0269.C8631, NewCertificates0269.C8632, NewCertificates0269.C8633, NewCertificates0269.C8634, NewCertificates0269.C8635, NewCertificates0269.C8636, NewCertificates0269.C8637, NewCertificates0269.C8638, NewCertificates0269.C8639, NewCertificates0270.C8640, NewCertificates0270.C8641, NewCertificates0270.C8642, NewCertificates0270.C8643, NewCertificates0270.C8644, NewCertificates0270.C8645, NewCertificates0270.C8646, NewCertificates0270.C8647, NewCertificates0270.C8648, NewCertificates0270.C8649, NewCertificates0270.C8650, NewCertificates0270.C8651, NewCertificates0270.C8652, NewCertificates0270.C8653, NewCertificates0270.C8654, NewCertificates0270.C8655, NewCertificates0270.C8656, NewCertificates0270.C8657, NewCertificates0270.C8658, NewCertificates0270.C8659, NewCertificates0270.C8660, NewCertificates0270.C8661, NewCertificates0270.C8662, NewCertificates0270.C8663, NewCertificates0270.C8664, NewCertificates0270.C8665, NewCertificates0270.C8666, NewCertificates0270.C8667}
def U0 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 1, 0, 1, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 2, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 1, 1; 2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,2)}
theorem doubled_enumeration : ((supportEdges 1022977272027660292).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1022977272027660292 D i ∧ offSum 1022977272027660292 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1022977272027660292 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1022977272027660292 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1022977272027660292 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1022977272027660292 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport183
