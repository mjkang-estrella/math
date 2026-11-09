import SignedCatalogue
import NewCertificates0015
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport010
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 4, 5, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0015.C480, NewCertificates0015.C481, NewCertificates0015.C482, NewCertificates0015.C483, NewCertificates0015.C484, NewCertificates0015.C485, NewCertificates0015.C486, NewCertificates0015.C487, NewCertificates0015.C488, NewCertificates0015.C489, NewCertificates0015.C490, NewCertificates0015.C491, NewCertificates0015.C492, NewCertificates0015.C493, NewCertificates0015.C494, NewCertificates0015.C495, NewCertificates0015.C496, NewCertificates0015.C497, NewCertificates0015.C498, NewCertificates0015.C499, NewCertificates0015.C500, NewCertificates0015.C501, NewCertificates0015.C502, NewCertificates0015.C503, NewCertificates0015.C504, NewCertificates0015.C505, NewCertificates0015.C506, NewCertificates0015.C507, NewCertificates0015.C508, NewCertificates0015.C509, NewCertificates0015.C510, NewCertificates0015.C511}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 807367439863021696).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 807367439863021696 D i ∧ offSum 807367439863021696 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 807367439863021696 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 807367439863021696 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 807367439863021696 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport010
