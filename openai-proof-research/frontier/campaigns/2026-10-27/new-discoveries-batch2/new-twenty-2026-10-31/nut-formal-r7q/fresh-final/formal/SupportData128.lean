import SignedCatalogue
import NewCertificates0191
import NewCertificates0192
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport128
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 4, 5, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0191.C6132, NewCertificates0191.C6133, NewCertificates0191.C6134, NewCertificates0191.C6135, NewCertificates0191.C6136, NewCertificates0191.C6137, NewCertificates0191.C6138, NewCertificates0191.C6139, NewCertificates0191.C6140, NewCertificates0191.C6141, NewCertificates0191.C6142, NewCertificates0191.C6143, NewCertificates0192.C6144, NewCertificates0192.C6145, NewCertificates0192.C6146, NewCertificates0192.C6147, NewCertificates0192.C6148, NewCertificates0192.C6149, NewCertificates0192.C6150, NewCertificates0192.C6151, NewCertificates0192.C6152, NewCertificates0192.C6153, NewCertificates0192.C6154, NewCertificates0192.C6155, NewCertificates0192.C6156, NewCertificates0192.C6157, NewCertificates0192.C6158, NewCertificates0192.C6159, NewCertificates0192.C6160, NewCertificates0192.C6161, NewCertificates0192.C6162, NewCertificates0192.C6163}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 1, 0, 0, 1, 0, 1, 0; 1, 0, 0, 0, 1, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 518286039098892480).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 518286039098892480 D i ∧ offSum 518286039098892480 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 518286039098892480 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 518286039098892480 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 518286039098892480 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 518286039098892480 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport128
