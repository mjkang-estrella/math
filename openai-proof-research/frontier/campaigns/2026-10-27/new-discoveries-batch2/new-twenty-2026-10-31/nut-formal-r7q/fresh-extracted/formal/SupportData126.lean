import SignedCatalogue
import NewCertificates0189
import NewCertificates0190
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport126
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 3, 1, 4, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0189.C6068, NewCertificates0189.C6069, NewCertificates0189.C6070, NewCertificates0189.C6071, NewCertificates0189.C6072, NewCertificates0189.C6073, NewCertificates0189.C6074, NewCertificates0189.C6075, NewCertificates0189.C6076, NewCertificates0189.C6077, NewCertificates0189.C6078, NewCertificates0189.C6079, NewCertificates0190.C6080, NewCertificates0190.C6081, NewCertificates0190.C6082, NewCertificates0190.C6083, NewCertificates0190.C6084, NewCertificates0190.C6085, NewCertificates0190.C6086, NewCertificates0190.C6087, NewCertificates0190.C6088, NewCertificates0190.C6089, NewCertificates0190.C6090, NewCertificates0190.C6091, NewCertificates0190.C6092, NewCertificates0190.C6093, NewCertificates0190.C6094, NewCertificates0190.C6095, NewCertificates0190.C6096, NewCertificates0190.C6097, NewCertificates0190.C6098, NewCertificates0190.C6099}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 508091111136338112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 508091111136338112 D i ∧ offSum 508091111136338112 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 508091111136338112 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 508091111136338112 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 508091111136338112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport126
