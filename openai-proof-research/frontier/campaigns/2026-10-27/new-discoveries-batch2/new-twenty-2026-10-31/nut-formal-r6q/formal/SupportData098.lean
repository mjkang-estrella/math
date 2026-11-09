import SignedCatalogue
import NewCertificates0141
import NewCertificates0142
import NewCertificates0143
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport098
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 3, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0141.C4542, NewCertificates0141.C4543, NewCertificates0142.C4544, NewCertificates0142.C4545, NewCertificates0142.C4546, NewCertificates0142.C4547, NewCertificates0142.C4548, NewCertificates0142.C4549, NewCertificates0142.C4550, NewCertificates0142.C4551, NewCertificates0142.C4552, NewCertificates0142.C4553, NewCertificates0142.C4554, NewCertificates0142.C4555, NewCertificates0142.C4556, NewCertificates0142.C4557, NewCertificates0142.C4558, NewCertificates0142.C4559, NewCertificates0142.C4560, NewCertificates0142.C4561, NewCertificates0142.C4562, NewCertificates0142.C4563, NewCertificates0142.C4564, NewCertificates0142.C4565, NewCertificates0142.C4566, NewCertificates0142.C4567, NewCertificates0142.C4568, NewCertificates0142.C4569, NewCertificates0142.C4570, NewCertificates0142.C4571, NewCertificates0142.C4572, NewCertificates0142.C4573, NewCertificates0142.C4574, NewCertificates0142.C4575, NewCertificates0143.C4576, NewCertificates0143.C4577, NewCertificates0143.C4578, NewCertificates0143.C4579, NewCertificates0143.C4580, NewCertificates0143.C4581, NewCertificates0143.C4582, NewCertificates0143.C4583, NewCertificates0143.C4584, NewCertificates0143.C4585, NewCertificates0143.C4586, NewCertificates0143.C4587, NewCertificates0143.C4588, NewCertificates0143.C4589}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
theorem doubled_enumeration : ((supportEdges 3545675170228209792).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545675170228209792 D i ∧ offSum 3545675170228209792 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 3545675170228209792 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3545675170228209792 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545675170228209792 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545675170228209792 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport098
