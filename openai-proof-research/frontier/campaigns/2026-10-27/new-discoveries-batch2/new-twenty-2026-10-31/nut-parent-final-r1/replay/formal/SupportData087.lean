import SignedCatalogue
import NewCertificates0125
import NewCertificates0126
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport087
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 4, 5, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0125.C4030, NewCertificates0125.C4031, NewCertificates0126.C4032, NewCertificates0126.C4033, NewCertificates0126.C4034, NewCertificates0126.C4035, NewCertificates0126.C4036, NewCertificates0126.C4037, NewCertificates0126.C4038, NewCertificates0126.C4039, NewCertificates0126.C4040, NewCertificates0126.C4041, NewCertificates0126.C4042, NewCertificates0126.C4043, NewCertificates0126.C4044, NewCertificates0126.C4045, NewCertificates0126.C4046, NewCertificates0126.C4047, NewCertificates0126.C4048, NewCertificates0126.C4049, NewCertificates0126.C4050, NewCertificates0126.C4051, NewCertificates0126.C4052, NewCertificates0126.C4053, NewCertificates0126.C4054, NewCertificates0126.C4055, NewCertificates0126.C4056, NewCertificates0126.C4057, NewCertificates0126.C4058, NewCertificates0126.C4059, NewCertificates0126.C4060, NewCertificates0126.C4061}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 1, 0, 0, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 800546044761903232).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 800546044761903232 D i ∧ offSum 800546044761903232 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 800546044761903232 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 800546044761903232 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 800546044761903232 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport087
