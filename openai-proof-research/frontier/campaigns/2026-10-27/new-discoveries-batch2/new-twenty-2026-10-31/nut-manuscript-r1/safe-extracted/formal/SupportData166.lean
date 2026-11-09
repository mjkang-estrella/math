import SignedCatalogue
import NewCertificates0242
import NewCertificates0243
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport166
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 6, 7, 1, 2, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0242.C7748, NewCertificates0242.C7749, NewCertificates0242.C7750, NewCertificates0242.C7751, NewCertificates0242.C7752, NewCertificates0242.C7753, NewCertificates0242.C7754, NewCertificates0242.C7755, NewCertificates0242.C7756, NewCertificates0242.C7757, NewCertificates0242.C7758, NewCertificates0242.C7759, NewCertificates0242.C7760, NewCertificates0242.C7761, NewCertificates0242.C7762, NewCertificates0242.C7763, NewCertificates0242.C7764, NewCertificates0242.C7765, NewCertificates0242.C7766, NewCertificates0242.C7767, NewCertificates0242.C7768, NewCertificates0242.C7769, NewCertificates0242.C7770, NewCertificates0242.C7771, NewCertificates0242.C7772, NewCertificates0242.C7773, NewCertificates0242.C7774, NewCertificates0242.C7775, NewCertificates0243.C7776, NewCertificates0243.C7777, NewCertificates0243.C7778, NewCertificates0243.C7779}
def U0 : QuotientMatrix := !![0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 946674076579557600).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 946674076579557600 D i ∧ offSum 946674076579557600 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 946674076579557600 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 946674076579557600 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 946674076579557600 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport166
