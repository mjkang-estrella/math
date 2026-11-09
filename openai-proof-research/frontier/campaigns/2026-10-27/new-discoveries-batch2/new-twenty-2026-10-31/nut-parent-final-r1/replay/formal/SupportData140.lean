import SignedCatalogue
import NewCertificates0203
import NewCertificates0204
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport140
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 5, 2, 4, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0203.C6516, NewCertificates0203.C6517, NewCertificates0203.C6518, NewCertificates0203.C6519, NewCertificates0203.C6520, NewCertificates0203.C6521, NewCertificates0203.C6522, NewCertificates0203.C6523, NewCertificates0203.C6524, NewCertificates0203.C6525, NewCertificates0203.C6526, NewCertificates0203.C6527, NewCertificates0204.C6528, NewCertificates0204.C6529, NewCertificates0204.C6530, NewCertificates0204.C6531, NewCertificates0204.C6532, NewCertificates0204.C6533, NewCertificates0204.C6534, NewCertificates0204.C6535, NewCertificates0204.C6536, NewCertificates0204.C6537, NewCertificates0204.C6538, NewCertificates0204.C6539, NewCertificates0204.C6540, NewCertificates0204.C6541, NewCertificates0204.C6542, NewCertificates0204.C6543, NewCertificates0204.C6544, NewCertificates0204.C6545, NewCertificates0204.C6546, NewCertificates0204.C6547}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1524827508781363392).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1524827508781363392 D i ∧ offSum 1524827508781363392 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1524827508781363392 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1524827508781363392 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1524827508781363392 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport140
