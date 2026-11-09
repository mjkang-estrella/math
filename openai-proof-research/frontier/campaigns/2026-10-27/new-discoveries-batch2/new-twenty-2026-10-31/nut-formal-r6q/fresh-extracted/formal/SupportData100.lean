import SignedCatalogue
import NewCertificates0144
import NewCertificates0145
import NewCertificates0146
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport100
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 6, 2, 3, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 4, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0144.C4638, NewCertificates0144.C4639, NewCertificates0145.C4640, NewCertificates0145.C4641, NewCertificates0145.C4642, NewCertificates0145.C4643, NewCertificates0145.C4644, NewCertificates0145.C4645, NewCertificates0145.C4646, NewCertificates0145.C4647, NewCertificates0145.C4648, NewCertificates0145.C4649, NewCertificates0145.C4650, NewCertificates0145.C4651, NewCertificates0145.C4652, NewCertificates0145.C4653, NewCertificates0145.C4654, NewCertificates0145.C4655, NewCertificates0145.C4656, NewCertificates0145.C4657, NewCertificates0145.C4658, NewCertificates0145.C4659, NewCertificates0145.C4660, NewCertificates0145.C4661, NewCertificates0145.C4662, NewCertificates0145.C4663, NewCertificates0145.C4664, NewCertificates0145.C4665, NewCertificates0145.C4666, NewCertificates0145.C4667, NewCertificates0145.C4668, NewCertificates0145.C4669, NewCertificates0145.C4670, NewCertificates0145.C4671, NewCertificates0146.C4672, NewCertificates0146.C4673, NewCertificates0146.C4674, NewCertificates0146.C4675, NewCertificates0146.C4676, NewCertificates0146.C4677, NewCertificates0146.C4678, NewCertificates0146.C4679, NewCertificates0146.C4680, NewCertificates0146.C4681, NewCertificates0146.C4682, NewCertificates0146.C4683, NewCertificates0146.C4684, NewCertificates0146.C4685, NewCertificates0146.C4686, NewCertificates0146.C4687, NewCertificates0146.C4688, NewCertificates0146.C4689, NewCertificates0146.C4690, NewCertificates0146.C4691, NewCertificates0146.C4692, NewCertificates0146.C4693, NewCertificates0146.C4694, NewCertificates0146.C4695, NewCertificates0146.C4696, NewCertificates0146.C4697, NewCertificates0146.C4698, NewCertificates0146.C4699, NewCertificates0146.C4700, NewCertificates0146.C4701}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 3545688467244058752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545688467244058752 D i ∧ offSum 3545688467244058752 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 3545688467244058752 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3545688467244058752 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 3545688467244058752 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545688467244058752 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545688467244058752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport100
