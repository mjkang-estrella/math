import SignedCatalogue
import NewCertificates0169
import NewCertificates0170
import NewCertificates0171
import NewCertificates0172
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport112
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 4, 5, 1, 7, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0169.C5408, NewCertificates0169.C5409, NewCertificates0169.C5410, NewCertificates0169.C5411, NewCertificates0169.C5412, NewCertificates0169.C5413, NewCertificates0169.C5414, NewCertificates0169.C5415, NewCertificates0169.C5416, NewCertificates0169.C5417, NewCertificates0169.C5418, NewCertificates0169.C5419, NewCertificates0169.C5420, NewCertificates0169.C5421, NewCertificates0169.C5422, NewCertificates0169.C5423, NewCertificates0169.C5424, NewCertificates0169.C5425, NewCertificates0169.C5426, NewCertificates0169.C5427, NewCertificates0169.C5428, NewCertificates0169.C5429, NewCertificates0169.C5430, NewCertificates0169.C5431, NewCertificates0169.C5432, NewCertificates0169.C5433, NewCertificates0169.C5434, NewCertificates0169.C5435, NewCertificates0169.C5436, NewCertificates0169.C5437, NewCertificates0169.C5438, NewCertificates0169.C5439, NewCertificates0170.C5440, NewCertificates0170.C5441, NewCertificates0170.C5442, NewCertificates0170.C5443, NewCertificates0170.C5444, NewCertificates0170.C5445, NewCertificates0170.C5446, NewCertificates0170.C5447, NewCertificates0170.C5448, NewCertificates0170.C5449, NewCertificates0170.C5450, NewCertificates0170.C5451, NewCertificates0170.C5452, NewCertificates0170.C5453, NewCertificates0170.C5454, NewCertificates0170.C5455, NewCertificates0170.C5456, NewCertificates0170.C5457, NewCertificates0170.C5458, NewCertificates0170.C5459, NewCertificates0170.C5460, NewCertificates0170.C5461, NewCertificates0170.C5462, NewCertificates0170.C5463, NewCertificates0170.C5464, NewCertificates0170.C5465, NewCertificates0170.C5466, NewCertificates0170.C5467, NewCertificates0170.C5468, NewCertificates0170.C5469, NewCertificates0170.C5470, NewCertificates0170.C5471, NewCertificates0171.C5472, NewCertificates0171.C5473, NewCertificates0171.C5474, NewCertificates0171.C5475, NewCertificates0171.C5476, NewCertificates0171.C5477, NewCertificates0171.C5478, NewCertificates0171.C5479, NewCertificates0171.C5480, NewCertificates0171.C5481, NewCertificates0171.C5482, NewCertificates0171.C5483, NewCertificates0171.C5484, NewCertificates0171.C5485, NewCertificates0171.C5486, NewCertificates0171.C5487, NewCertificates0171.C5488, NewCertificates0171.C5489, NewCertificates0171.C5490, NewCertificates0171.C5491, NewCertificates0171.C5492, NewCertificates0171.C5493, NewCertificates0171.C5494, NewCertificates0171.C5495, NewCertificates0171.C5496, NewCertificates0171.C5497, NewCertificates0171.C5498, NewCertificates0171.C5499, NewCertificates0171.C5500, NewCertificates0171.C5501, NewCertificates0171.C5502, NewCertificates0171.C5503, NewCertificates0172.C5504, NewCertificates0172.C5505, NewCertificates0172.C5506, NewCertificates0172.C5507}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 1, 0, 0, 0, 1, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U9 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 2, 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U12 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U13 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U14 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U15 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,3), (4,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(4,6)}
def D7 : Finset (Fin 8 × Fin 8) := {(2,3), (4,6)}
def D8 : Finset (Fin 8 × Fin 8) := {(1,5), (4,6)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,5), (2,3), (4,6)}
def D10 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D11 : Finset (Fin 8 × Fin 8) := {(0,6), (2,3)}
def D12 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5)}
def D13 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (2,3)}
def D14 : Finset (Fin 8 × Fin 8) := {(0,6), (4,5)}
def D15 : Finset (Fin 8 × Fin 8) := {(0,6), (2,3), (4,5)}
theorem doubled_enumeration : ((supportEdges 1013611596884779072).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1013611596884779072 D i ∧ offSum 1013611596884779072 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15} := by
  decide +kernel
theorem augmentation0 : augmentation 1013611596884779072 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1013611596884779072 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1013611596884779072 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1013611596884779072 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 1013611596884779072 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 1013611596884779072 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 1013611596884779072 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 1013611596884779072 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 1013611596884779072 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 1013611596884779072 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 1013611596884779072 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 1013611596884779072 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 1013611596884779072 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 1013611596884779072 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 1013611596884779072 D14 = U14 := by
  decide +kernel
theorem augmentation15 : augmentation 1013611596884779072 D15 = U15 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1013611596884779072 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14, augmentation15]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1013611596884779072 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport112
