import SignedCatalogue
import NewCertificates0146
import NewCertificates0147
import NewCertificates0148
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport101
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 3, 4, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0146.C4702, NewCertificates0146.C4703, NewCertificates0147.C4704, NewCertificates0147.C4705, NewCertificates0147.C4706, NewCertificates0147.C4707, NewCertificates0147.C4708, NewCertificates0147.C4709, NewCertificates0147.C4710, NewCertificates0147.C4711, NewCertificates0147.C4712, NewCertificates0147.C4713, NewCertificates0147.C4714, NewCertificates0147.C4715, NewCertificates0147.C4716, NewCertificates0147.C4717, NewCertificates0147.C4718, NewCertificates0147.C4719, NewCertificates0147.C4720, NewCertificates0147.C4721, NewCertificates0147.C4722, NewCertificates0147.C4723, NewCertificates0147.C4724, NewCertificates0147.C4725, NewCertificates0147.C4726, NewCertificates0147.C4727, NewCertificates0147.C4728, NewCertificates0147.C4729, NewCertificates0147.C4730, NewCertificates0147.C4731, NewCertificates0147.C4732, NewCertificates0147.C4733, NewCertificates0147.C4734, NewCertificates0147.C4735, NewCertificates0148.C4736, NewCertificates0148.C4737, NewCertificates0148.C4738, NewCertificates0148.C4739, NewCertificates0148.C4740, NewCertificates0148.C4741, NewCertificates0148.C4742, NewCertificates0148.C4743, NewCertificates0148.C4744, NewCertificates0148.C4745, NewCertificates0148.C4746, NewCertificates0148.C4747, NewCertificates0148.C4748, NewCertificates0148.C4749, NewCertificates0148.C4750, NewCertificates0148.C4751, NewCertificates0148.C4752, NewCertificates0148.C4753, NewCertificates0148.C4754, NewCertificates0148.C4755, NewCertificates0148.C4756, NewCertificates0148.C4757}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 1, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 1, 0, 1, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 1, 1; 0, 0, 1, 1, 0, 1, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,3), (2,4)}
theorem doubled_enumeration : ((supportEdges 2534629544452720768).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2534629544452720768 D i ∧ offSum 2534629544452720768 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 2534629544452720768 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2534629544452720768 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 2534629544452720768 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 2534629544452720768 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2534629544452720768 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2534629544452720768 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport101
