import SignedCatalogue
import NewCertificates0163
import NewCertificates0164
import NewCertificates0165
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport110
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 4, 3, 7, 1, 2, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 4, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0163.C5216, NewCertificates0163.C5217, NewCertificates0163.C5218, NewCertificates0163.C5219, NewCertificates0163.C5220, NewCertificates0163.C5221, NewCertificates0163.C5222, NewCertificates0163.C5223, NewCertificates0163.C5224, NewCertificates0163.C5225, NewCertificates0163.C5226, NewCertificates0163.C5227, NewCertificates0163.C5228, NewCertificates0163.C5229, NewCertificates0163.C5230, NewCertificates0163.C5231, NewCertificates0163.C5232, NewCertificates0163.C5233, NewCertificates0163.C5234, NewCertificates0163.C5235, NewCertificates0163.C5236, NewCertificates0163.C5237, NewCertificates0163.C5238, NewCertificates0163.C5239, NewCertificates0163.C5240, NewCertificates0163.C5241, NewCertificates0163.C5242, NewCertificates0163.C5243, NewCertificates0163.C5244, NewCertificates0163.C5245, NewCertificates0163.C5246, NewCertificates0163.C5247, NewCertificates0164.C5248, NewCertificates0164.C5249, NewCertificates0164.C5250, NewCertificates0164.C5251, NewCertificates0164.C5252, NewCertificates0164.C5253, NewCertificates0164.C5254, NewCertificates0164.C5255, NewCertificates0164.C5256, NewCertificates0164.C5257, NewCertificates0164.C5258, NewCertificates0164.C5259, NewCertificates0164.C5260, NewCertificates0164.C5261, NewCertificates0164.C5262, NewCertificates0164.C5263, NewCertificates0164.C5264, NewCertificates0164.C5265, NewCertificates0164.C5266, NewCertificates0164.C5267, NewCertificates0164.C5268, NewCertificates0164.C5269, NewCertificates0164.C5270, NewCertificates0164.C5271, NewCertificates0164.C5272, NewCertificates0164.C5273, NewCertificates0164.C5274, NewCertificates0164.C5275, NewCertificates0164.C5276, NewCertificates0164.C5277, NewCertificates0164.C5278, NewCertificates0164.C5279, NewCertificates0165.C5280, NewCertificates0165.C5281, NewCertificates0165.C5282, NewCertificates0165.C5283, NewCertificates0165.C5284, NewCertificates0165.C5285, NewCertificates0165.C5286, NewCertificates0165.C5287, NewCertificates0165.C5288, NewCertificates0165.C5289, NewCertificates0165.C5290, NewCertificates0165.C5291, NewCertificates0165.C5292, NewCertificates0165.C5293, NewCertificates0165.C5294, NewCertificates0165.C5295, NewCertificates0165.C5296, NewCertificates0165.C5297, NewCertificates0165.C5298, NewCertificates0165.C5299, NewCertificates0165.C5300, NewCertificates0165.C5301, NewCertificates0165.C5302, NewCertificates0165.C5303, NewCertificates0165.C5304, NewCertificates0165.C5305, NewCertificates0165.C5306, NewCertificates0165.C5307, NewCertificates0165.C5308, NewCertificates0165.C5309, NewCertificates0165.C5310, NewCertificates0165.C5311}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 1, 2, 0, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0, 2, 0; 0, 2, 1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U9 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U12 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U13 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 1, 2, 0, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U14 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 2, 1, 0, 0, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(4,6)}
def D7 : Finset (Fin 8 × Fin 8) := {(2,5), (4,6)}
def D8 : Finset (Fin 8 × Fin 8) := {(1,5), (4,6)}
def D9 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D10 : Finset (Fin 8 × Fin 8) := {(0,6), (2,5)}
def D11 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5)}
def D12 : Finset (Fin 8 × Fin 8) := {(0,6), (3,4)}
def D13 : Finset (Fin 8 × Fin 8) := {(0,6), (2,5), (3,4)}
def D14 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 1013598299868930112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1013598299868930112 D i ∧ offSum 1013598299868930112 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14} := by
  decide +kernel
theorem augmentation0 : augmentation 1013598299868930112 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1013598299868930112 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1013598299868930112 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1013598299868930112 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 1013598299868930112 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 1013598299868930112 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 1013598299868930112 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 1013598299868930112 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 1013598299868930112 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 1013598299868930112 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 1013598299868930112 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 1013598299868930112 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 1013598299868930112 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 1013598299868930112 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 1013598299868930112 D14 = U14 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1013598299868930112 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1013598299868930112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport110
