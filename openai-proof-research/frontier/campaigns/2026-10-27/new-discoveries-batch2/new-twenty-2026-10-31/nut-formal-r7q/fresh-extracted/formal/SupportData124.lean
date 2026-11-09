import SignedCatalogue
import NewCertificates0188
import NewCertificates0189
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport124
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 5, 1, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0188.C6036, NewCertificates0188.C6037, NewCertificates0188.C6038, NewCertificates0188.C6039, NewCertificates0188.C6040, NewCertificates0188.C6041, NewCertificates0188.C6042, NewCertificates0188.C6043, NewCertificates0188.C6044, NewCertificates0188.C6045, NewCertificates0188.C6046, NewCertificates0188.C6047, NewCertificates0189.C6048, NewCertificates0189.C6049, NewCertificates0189.C6050, NewCertificates0189.C6051}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1379590826825392320).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1379590826825392320 D i ∧ offSum 1379590826825392320 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1379590826825392320 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1379590826825392320 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1379590826825392320 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport124
