import SignedCatalogue
import NewCertificates0132
import NewCertificates0133
import NewCertificates0134
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport092
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 2, 3, 1, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 3]
def matrices : Finset QuotientMatrix := {NewCertificates0132.C4238, NewCertificates0132.C4239, NewCertificates0132.C4240, NewCertificates0132.C4241, NewCertificates0132.C4242, NewCertificates0132.C4243, NewCertificates0132.C4244, NewCertificates0132.C4245, NewCertificates0132.C4246, NewCertificates0132.C4247, NewCertificates0132.C4248, NewCertificates0132.C4249, NewCertificates0132.C4250, NewCertificates0132.C4251, NewCertificates0132.C4252, NewCertificates0132.C4253, NewCertificates0132.C4254, NewCertificates0132.C4255, NewCertificates0133.C4256, NewCertificates0133.C4257, NewCertificates0133.C4258, NewCertificates0133.C4259, NewCertificates0133.C4260, NewCertificates0133.C4261, NewCertificates0133.C4262, NewCertificates0133.C4263, NewCertificates0133.C4264, NewCertificates0133.C4265, NewCertificates0133.C4266, NewCertificates0133.C4267, NewCertificates0133.C4268, NewCertificates0133.C4269, NewCertificates0133.C4270, NewCertificates0133.C4271, NewCertificates0133.C4272, NewCertificates0133.C4273, NewCertificates0133.C4274, NewCertificates0133.C4275, NewCertificates0133.C4276, NewCertificates0133.C4277, NewCertificates0133.C4278, NewCertificates0133.C4279, NewCertificates0133.C4280, NewCertificates0133.C4281, NewCertificates0133.C4282, NewCertificates0133.C4283, NewCertificates0133.C4284, NewCertificates0133.C4285, NewCertificates0133.C4286, NewCertificates0133.C4287, NewCertificates0134.C4288, NewCertificates0134.C4289, NewCertificates0134.C4290, NewCertificates0134.C4291, NewCertificates0134.C4292, NewCertificates0134.C4293}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7030836183981117568).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7030836183981117568 D i ∧ offSum 7030836183981117568 D i ≤ 3) = {D0, D1, D2, D3} := by
  decide +kernel
theorem augmentation0 : augmentation 7030836183981117568 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7030836183981117568 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7030836183981117568 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7030836183981117568 D3 = U3 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7030836183981117568 = {U0, U1, U2, U3} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7030836183981117568 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport092
