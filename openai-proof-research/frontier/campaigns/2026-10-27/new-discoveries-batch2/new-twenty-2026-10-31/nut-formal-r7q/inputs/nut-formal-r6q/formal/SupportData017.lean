import SignedCatalogue
import NewCertificates0025
import NewCertificates0026
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport017
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 3, 5, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0025.C824, NewCertificates0025.C825, NewCertificates0025.C826, NewCertificates0025.C827, NewCertificates0025.C828, NewCertificates0025.C829, NewCertificates0025.C830, NewCertificates0025.C831, NewCertificates0026.C832, NewCertificates0026.C833, NewCertificates0026.C834, NewCertificates0026.C835, NewCertificates0026.C836, NewCertificates0026.C837, NewCertificates0026.C838, NewCertificates0026.C839, NewCertificates0026.C840, NewCertificates0026.C841, NewCertificates0026.C842, NewCertificates0026.C843, NewCertificates0026.C844, NewCertificates0026.C845, NewCertificates0026.C846, NewCertificates0026.C847, NewCertificates0026.C848, NewCertificates0026.C849, NewCertificates0026.C850, NewCertificates0026.C851, NewCertificates0026.C852, NewCertificates0026.C853, NewCertificates0026.C854, NewCertificates0026.C855}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1381572267575640192).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1381572267575640192 D i ∧ offSum 1381572267575640192 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1381572267575640192 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1381572267575640192 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1381572267575640192 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport017
