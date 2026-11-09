import SignedCatalogue
import NewCertificates0205
import NewCertificates0206
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport142
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 3, 2, 4, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0205.C6580, NewCertificates0205.C6581, NewCertificates0205.C6582, NewCertificates0205.C6583, NewCertificates0205.C6584, NewCertificates0205.C6585, NewCertificates0205.C6586, NewCertificates0205.C6587, NewCertificates0205.C6588, NewCertificates0205.C6589, NewCertificates0205.C6590, NewCertificates0205.C6591, NewCertificates0206.C6592, NewCertificates0206.C6593, NewCertificates0206.C6594, NewCertificates0206.C6595, NewCertificates0206.C6596, NewCertificates0206.C6597, NewCertificates0206.C6598, NewCertificates0206.C6599, NewCertificates0206.C6600, NewCertificates0206.C6601, NewCertificates0206.C6602, NewCertificates0206.C6603, NewCertificates0206.C6604, NewCertificates0206.C6605, NewCertificates0206.C6606, NewCertificates0206.C6607, NewCertificates0206.C6608, NewCertificates0206.C6609, NewCertificates0206.C6610, NewCertificates0206.C6611}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 0, 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 5010560431491133632).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5010560431491133632 D i ∧ offSum 5010560431491133632 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 5010560431491133632 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5010560431491133632 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5010560431491133632 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport142
