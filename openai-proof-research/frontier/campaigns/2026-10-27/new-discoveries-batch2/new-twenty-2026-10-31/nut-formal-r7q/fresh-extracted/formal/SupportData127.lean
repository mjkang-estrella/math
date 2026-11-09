import SignedCatalogue
import NewCertificates0190
import NewCertificates0191
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport127
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 3, 1, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0190.C6100, NewCertificates0190.C6101, NewCertificates0190.C6102, NewCertificates0190.C6103, NewCertificates0190.C6104, NewCertificates0190.C6105, NewCertificates0190.C6106, NewCertificates0190.C6107, NewCertificates0190.C6108, NewCertificates0190.C6109, NewCertificates0190.C6110, NewCertificates0190.C6111, NewCertificates0191.C6112, NewCertificates0191.C6113, NewCertificates0191.C6114, NewCertificates0191.C6115, NewCertificates0191.C6116, NewCertificates0191.C6117, NewCertificates0191.C6118, NewCertificates0191.C6119, NewCertificates0191.C6120, NewCertificates0191.C6121, NewCertificates0191.C6122, NewCertificates0191.C6123, NewCertificates0191.C6124, NewCertificates0191.C6125, NewCertificates0191.C6126, NewCertificates0191.C6127, NewCertificates0191.C6128, NewCertificates0191.C6129, NewCertificates0191.C6130, NewCertificates0191.C6131}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1372769457762508992).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1372769457762508992 D i ∧ offSum 1372769457762508992 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1372769457762508992 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1372769457762508992 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1372769457762508992 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport127
