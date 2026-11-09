import SignedCatalogue
import NewCertificates0204
import NewCertificates0205
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport141
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 4, 2, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0204.C6548, NewCertificates0204.C6549, NewCertificates0204.C6550, NewCertificates0204.C6551, NewCertificates0204.C6552, NewCertificates0204.C6553, NewCertificates0204.C6554, NewCertificates0204.C6555, NewCertificates0204.C6556, NewCertificates0204.C6557, NewCertificates0204.C6558, NewCertificates0204.C6559, NewCertificates0205.C6560, NewCertificates0205.C6561, NewCertificates0205.C6562, NewCertificates0205.C6563, NewCertificates0205.C6564, NewCertificates0205.C6565, NewCertificates0205.C6566, NewCertificates0205.C6567, NewCertificates0205.C6568, NewCertificates0205.C6569, NewCertificates0205.C6570, NewCertificates0205.C6571, NewCertificates0205.C6572, NewCertificates0205.C6573, NewCertificates0205.C6574, NewCertificates0205.C6575, NewCertificates0205.C6576, NewCertificates0205.C6577, NewCertificates0205.C6578, NewCertificates0205.C6579}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 0, 1; 1, 0, 0, 1, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 2673315507627110592).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2673315507627110592 D i ∧ offSum 2673315507627110592 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 2673315507627110592 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2673315507627110592 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2673315507627110592 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport141
