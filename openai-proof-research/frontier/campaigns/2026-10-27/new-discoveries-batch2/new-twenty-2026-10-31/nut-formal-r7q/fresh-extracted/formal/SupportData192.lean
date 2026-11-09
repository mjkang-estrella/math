import SignedCatalogue
import NewCertificates0283
import NewCertificates0284
import NewCertificates0285
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport192
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 1, 7, 6, 2, 3, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0283.C9076, NewCertificates0283.C9077, NewCertificates0283.C9078, NewCertificates0283.C9079, NewCertificates0283.C9080, NewCertificates0283.C9081, NewCertificates0283.C9082, NewCertificates0283.C9083, NewCertificates0283.C9084, NewCertificates0283.C9085, NewCertificates0283.C9086, NewCertificates0283.C9087, NewCertificates0284.C9088, NewCertificates0284.C9089, NewCertificates0284.C9090, NewCertificates0284.C9091, NewCertificates0284.C9092, NewCertificates0284.C9093, NewCertificates0284.C9094, NewCertificates0284.C9095, NewCertificates0284.C9096, NewCertificates0284.C9097, NewCertificates0284.C9098, NewCertificates0284.C9099, NewCertificates0284.C9100, NewCertificates0284.C9101, NewCertificates0284.C9102, NewCertificates0284.C9103, NewCertificates0284.C9104, NewCertificates0284.C9105, NewCertificates0284.C9106, NewCertificates0284.C9107, NewCertificates0284.C9108, NewCertificates0284.C9109, NewCertificates0284.C9110, NewCertificates0284.C9111, NewCertificates0284.C9112, NewCertificates0284.C9113, NewCertificates0284.C9114, NewCertificates0284.C9115, NewCertificates0284.C9116, NewCertificates0284.C9117, NewCertificates0284.C9118, NewCertificates0284.C9119, NewCertificates0285.C9120, NewCertificates0285.C9121, NewCertificates0285.C9122, NewCertificates0285.C9123}
def U0 : QuotientMatrix := !![1, 1, 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(0,1)}
theorem doubled_enumeration : ((supportEdges 5010848512597836162).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010848512597836162 D i ∧ offSum 5010848512597836162 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 5010848512597836162 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5010848512597836162 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010848512597836162 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010848512597836162 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport192
