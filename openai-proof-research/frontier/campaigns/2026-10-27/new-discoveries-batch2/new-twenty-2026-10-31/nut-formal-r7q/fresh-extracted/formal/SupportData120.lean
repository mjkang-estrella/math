import SignedCatalogue
import NewCertificates0178
import NewCertificates0179
import NewCertificates0180
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport120
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 4, 1, 3, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 2, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0178.C5724, NewCertificates0178.C5725, NewCertificates0178.C5726, NewCertificates0178.C5727, NewCertificates0179.C5728, NewCertificates0179.C5729, NewCertificates0179.C5730, NewCertificates0179.C5731, NewCertificates0179.C5732, NewCertificates0179.C5733, NewCertificates0179.C5734, NewCertificates0179.C5735, NewCertificates0179.C5736, NewCertificates0179.C5737, NewCertificates0179.C5738, NewCertificates0179.C5739, NewCertificates0179.C5740, NewCertificates0179.C5741, NewCertificates0179.C5742, NewCertificates0179.C5743, NewCertificates0179.C5744, NewCertificates0179.C5745, NewCertificates0179.C5746, NewCertificates0179.C5747, NewCertificates0179.C5748, NewCertificates0179.C5749, NewCertificates0179.C5750, NewCertificates0179.C5751, NewCertificates0179.C5752, NewCertificates0179.C5753, NewCertificates0179.C5754, NewCertificates0179.C5755, NewCertificates0179.C5756, NewCertificates0179.C5757, NewCertificates0179.C5758, NewCertificates0179.C5759, NewCertificates0180.C5760, NewCertificates0180.C5761, NewCertificates0180.C5762, NewCertificates0180.C5763, NewCertificates0180.C5764, NewCertificates0180.C5765, NewCertificates0180.C5766, NewCertificates0180.C5767, NewCertificates0180.C5768, NewCertificates0180.C5769, NewCertificates0180.C5770, NewCertificates0180.C5771}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 798551417657794752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 798551417657794752 D i ∧ offSum 798551417657794752 D i ≤ 3) = {D0, D1, D2, D3, D4, D5} := by
  decide +kernel
theorem augmentation0 : augmentation 798551417657794752 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 798551417657794752 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 798551417657794752 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 798551417657794752 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 798551417657794752 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 798551417657794752 D5 = U5 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 798551417657794752 = {U0, U1, U2, U3, U4, U5} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 798551417657794752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport120
