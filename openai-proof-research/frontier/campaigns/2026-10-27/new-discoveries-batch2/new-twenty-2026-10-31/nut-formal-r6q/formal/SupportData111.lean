import SignedCatalogue
import NewCertificates0166
import NewCertificates0167
import NewCertificates0168
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport111
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 1, 2, 5, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0166.C5312, NewCertificates0166.C5313, NewCertificates0166.C5314, NewCertificates0166.C5315, NewCertificates0166.C5316, NewCertificates0166.C5317, NewCertificates0166.C5318, NewCertificates0166.C5319, NewCertificates0166.C5320, NewCertificates0166.C5321, NewCertificates0166.C5322, NewCertificates0166.C5323, NewCertificates0166.C5324, NewCertificates0166.C5325, NewCertificates0166.C5326, NewCertificates0166.C5327, NewCertificates0166.C5328, NewCertificates0166.C5329, NewCertificates0166.C5330, NewCertificates0166.C5331, NewCertificates0166.C5332, NewCertificates0166.C5333, NewCertificates0166.C5334, NewCertificates0166.C5335, NewCertificates0166.C5336, NewCertificates0166.C5337, NewCertificates0166.C5338, NewCertificates0166.C5339, NewCertificates0166.C5340, NewCertificates0166.C5341, NewCertificates0166.C5342, NewCertificates0166.C5343, NewCertificates0167.C5344, NewCertificates0167.C5345, NewCertificates0167.C5346, NewCertificates0167.C5347, NewCertificates0167.C5348, NewCertificates0167.C5349, NewCertificates0167.C5350, NewCertificates0167.C5351, NewCertificates0167.C5352, NewCertificates0167.C5353, NewCertificates0167.C5354, NewCertificates0167.C5355, NewCertificates0167.C5356, NewCertificates0167.C5357, NewCertificates0167.C5358, NewCertificates0167.C5359, NewCertificates0167.C5360, NewCertificates0167.C5361, NewCertificates0167.C5362, NewCertificates0167.C5363, NewCertificates0167.C5364, NewCertificates0167.C5365, NewCertificates0167.C5366, NewCertificates0167.C5367, NewCertificates0167.C5368, NewCertificates0167.C5369, NewCertificates0167.C5370, NewCertificates0167.C5371, NewCertificates0167.C5372, NewCertificates0167.C5373, NewCertificates0167.C5374, NewCertificates0167.C5375, NewCertificates0168.C5376, NewCertificates0168.C5377, NewCertificates0168.C5378, NewCertificates0168.C5379, NewCertificates0168.C5380, NewCertificates0168.C5381, NewCertificates0168.C5382, NewCertificates0168.C5383, NewCertificates0168.C5384, NewCertificates0168.C5385, NewCertificates0168.C5386, NewCertificates0168.C5387, NewCertificates0168.C5388, NewCertificates0168.C5389, NewCertificates0168.C5390, NewCertificates0168.C5391, NewCertificates0168.C5392, NewCertificates0168.C5393, NewCertificates0168.C5394, NewCertificates0168.C5395, NewCertificates0168.C5396, NewCertificates0168.C5397, NewCertificates0168.C5398, NewCertificates0168.C5399, NewCertificates0168.C5400, NewCertificates0168.C5401, NewCertificates0168.C5402, NewCertificates0168.C5403, NewCertificates0168.C5404, NewCertificates0168.C5405, NewCertificates0168.C5406, NewCertificates0168.C5407}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U8 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U9 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U12 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U13 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U14 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def U15 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 1, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,4), (3,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D9 : Finset (Fin 8 × Fin 8) := {(0,6), (3,4)}
def D10 : Finset (Fin 8 × Fin 8) := {(0,6), (3,5)}
def D11 : Finset (Fin 8 × Fin 8) := {(0,6), (2,4)}
def D12 : Finset (Fin 8 × Fin 8) := {(0,6), (2,4), (3,5)}
def D13 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5)}
def D14 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (3,4)}
def D15 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 5080352902121300032).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5080352902121300032 D i ∧ offSum 5080352902121300032 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15} := by
  decide +kernel
theorem augmentation0 : augmentation 5080352902121300032 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5080352902121300032 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 5080352902121300032 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 5080352902121300032 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 5080352902121300032 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 5080352902121300032 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 5080352902121300032 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 5080352902121300032 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 5080352902121300032 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 5080352902121300032 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 5080352902121300032 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 5080352902121300032 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 5080352902121300032 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 5080352902121300032 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 5080352902121300032 D14 = U14 := by
  decide +kernel
theorem augmentation15 : augmentation 5080352902121300032 D15 = U15 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5080352902121300032 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14, augmentation15]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5080352902121300032 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport111
