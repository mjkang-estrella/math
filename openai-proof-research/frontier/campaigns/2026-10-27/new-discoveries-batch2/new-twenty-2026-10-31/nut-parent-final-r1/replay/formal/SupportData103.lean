import SignedCatalogue
import NewCertificates0150
import NewCertificates0151
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport103
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 3, 4, 5, 6, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0150.C4806, NewCertificates0150.C4807, NewCertificates0150.C4808, NewCertificates0150.C4809, NewCertificates0150.C4810, NewCertificates0150.C4811, NewCertificates0150.C4812, NewCertificates0150.C4813, NewCertificates0150.C4814, NewCertificates0150.C4815, NewCertificates0150.C4816, NewCertificates0150.C4817, NewCertificates0150.C4818, NewCertificates0150.C4819, NewCertificates0150.C4820, NewCertificates0150.C4821, NewCertificates0150.C4822, NewCertificates0150.C4823, NewCertificates0150.C4824, NewCertificates0150.C4825, NewCertificates0150.C4826, NewCertificates0150.C4827, NewCertificates0150.C4828, NewCertificates0150.C4829, NewCertificates0150.C4830, NewCertificates0150.C4831, NewCertificates0151.C4832, NewCertificates0151.C4833, NewCertificates0151.C4834, NewCertificates0151.C4835, NewCertificates0151.C4836, NewCertificates0151.C4837, NewCertificates0151.C4838, NewCertificates0151.C4839, NewCertificates0151.C4840, NewCertificates0151.C4841, NewCertificates0151.C4842, NewCertificates0151.C4843, NewCertificates0151.C4844, NewCertificates0151.C4845, NewCertificates0151.C4846, NewCertificates0151.C4847, NewCertificates0151.C4848, NewCertificates0151.C4849, NewCertificates0151.C4850, NewCertificates0151.C4851, NewCertificates0151.C4852, NewCertificates0151.C4853}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0; 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 1, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,2)}
theorem doubled_enumeration : ((supportEdges 1812233381598086272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1812233381598086272 D i ∧ offSum 1812233381598086272 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1812233381598086272 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1812233381598086272 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1812233381598086272 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1812233381598086272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport103
