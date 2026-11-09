import SignedCatalogue
import NewCertificates0135
import NewCertificates0136
import NewCertificates0137
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport094
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 5, 6, 2, 1, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0135.C4326, NewCertificates0135.C4327, NewCertificates0135.C4328, NewCertificates0135.C4329, NewCertificates0135.C4330, NewCertificates0135.C4331, NewCertificates0135.C4332, NewCertificates0135.C4333, NewCertificates0135.C4334, NewCertificates0135.C4335, NewCertificates0135.C4336, NewCertificates0135.C4337, NewCertificates0135.C4338, NewCertificates0135.C4339, NewCertificates0135.C4340, NewCertificates0135.C4341, NewCertificates0135.C4342, NewCertificates0135.C4343, NewCertificates0135.C4344, NewCertificates0135.C4345, NewCertificates0135.C4346, NewCertificates0135.C4347, NewCertificates0135.C4348, NewCertificates0135.C4349, NewCertificates0135.C4350, NewCertificates0135.C4351, NewCertificates0136.C4352, NewCertificates0136.C4353, NewCertificates0136.C4354, NewCertificates0136.C4355, NewCertificates0136.C4356, NewCertificates0136.C4357, NewCertificates0136.C4358, NewCertificates0136.C4359, NewCertificates0136.C4360, NewCertificates0136.C4361, NewCertificates0136.C4362, NewCertificates0136.C4363, NewCertificates0136.C4364, NewCertificates0136.C4365, NewCertificates0136.C4366, NewCertificates0136.C4367, NewCertificates0136.C4368, NewCertificates0136.C4369, NewCertificates0136.C4370, NewCertificates0136.C4371, NewCertificates0136.C4372, NewCertificates0136.C4373, NewCertificates0136.C4374, NewCertificates0136.C4375, NewCertificates0136.C4376, NewCertificates0136.C4377, NewCertificates0136.C4378, NewCertificates0136.C4379, NewCertificates0136.C4380, NewCertificates0136.C4381, NewCertificates0136.C4382, NewCertificates0136.C4383, NewCertificates0137.C4384, NewCertificates0137.C4385, NewCertificates0137.C4386, NewCertificates0137.C4387, NewCertificates0137.C4388, NewCertificates0137.C4389, NewCertificates0137.C4390, NewCertificates0137.C4391, NewCertificates0137.C4392, NewCertificates0137.C4393, NewCertificates0137.C4394, NewCertificates0137.C4395, NewCertificates0137.C4396, NewCertificates0137.C4397}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 1, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 0, 1, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 7035401115473039488).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 7035401115473039488 D i ∧ offSum 7035401115473039488 D i ≤ 3) = {D0, D1, D2, D3, D4} := by
  decide +kernel
theorem augmentation0 : augmentation 7035401115473039488 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 7035401115473039488 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 7035401115473039488 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 7035401115473039488 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 7035401115473039488 D4 = U4 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 7035401115473039488 = {U0, U1, U2, U3, U4} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 7035401115473039488 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport094
