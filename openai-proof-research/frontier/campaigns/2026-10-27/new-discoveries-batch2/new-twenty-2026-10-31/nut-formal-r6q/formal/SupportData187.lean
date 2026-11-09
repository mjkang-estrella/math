import SignedCatalogue
import NewCertificates0275
import NewCertificates0276
import NewCertificates0277
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport187
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 2, 1, 7, 3, 4, 5, 6] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0275.C8812, NewCertificates0275.C8813, NewCertificates0275.C8814, NewCertificates0275.C8815, NewCertificates0275.C8816, NewCertificates0275.C8817, NewCertificates0275.C8818, NewCertificates0275.C8819, NewCertificates0275.C8820, NewCertificates0275.C8821, NewCertificates0275.C8822, NewCertificates0275.C8823, NewCertificates0275.C8824, NewCertificates0275.C8825, NewCertificates0275.C8826, NewCertificates0275.C8827, NewCertificates0275.C8828, NewCertificates0275.C8829, NewCertificates0275.C8830, NewCertificates0275.C8831, NewCertificates0276.C8832, NewCertificates0276.C8833, NewCertificates0276.C8834, NewCertificates0276.C8835, NewCertificates0276.C8836, NewCertificates0276.C8837, NewCertificates0276.C8838, NewCertificates0276.C8839, NewCertificates0276.C8840, NewCertificates0276.C8841, NewCertificates0276.C8842, NewCertificates0276.C8843, NewCertificates0276.C8844, NewCertificates0276.C8845, NewCertificates0276.C8846, NewCertificates0276.C8847, NewCertificates0276.C8848, NewCertificates0276.C8849, NewCertificates0276.C8850, NewCertificates0276.C8851, NewCertificates0276.C8852, NewCertificates0276.C8853, NewCertificates0276.C8854, NewCertificates0276.C8855, NewCertificates0276.C8856, NewCertificates0276.C8857, NewCertificates0276.C8858, NewCertificates0276.C8859, NewCertificates0276.C8860, NewCertificates0276.C8861, NewCertificates0276.C8862, NewCertificates0276.C8863, NewCertificates0277.C8864, NewCertificates0277.C8865, NewCertificates0277.C8866, NewCertificates0277.C8867, NewCertificates0277.C8868, NewCertificates0277.C8869, NewCertificates0277.C8870, NewCertificates0277.C8871, NewCertificates0277.C8872, NewCertificates0277.C8873, NewCertificates0277.C8874, NewCertificates0277.C8875}
def U0 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 1; 1, 1, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 1, 0, 0, 0, 0, 0; 0, 0, 2, 0, 0, 0, 0, 1; 1, 2, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 2, 0, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0, 0, 1; 2, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
def D2 : Finset (Fin 8 × Fin 8) := {(0,2)}
theorem doubled_enumeration : ((supportEdges 1889357766536168452).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1889357766536168452 D i ∧ offSum 1889357766536168452 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 1889357766536168452 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1889357766536168452 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1889357766536168452 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1889357766536168452 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1889357766536168452 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport187
