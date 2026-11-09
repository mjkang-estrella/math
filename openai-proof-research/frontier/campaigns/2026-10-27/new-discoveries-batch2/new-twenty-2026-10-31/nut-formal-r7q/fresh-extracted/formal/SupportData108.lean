import SignedCatalogue
import NewCertificates0157
import NewCertificates0158
import NewCertificates0159
import NewCertificates0160
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport108
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 1, 7, 2, 3, 5, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0157.C5030, NewCertificates0157.C5031, NewCertificates0157.C5032, NewCertificates0157.C5033, NewCertificates0157.C5034, NewCertificates0157.C5035, NewCertificates0157.C5036, NewCertificates0157.C5037, NewCertificates0157.C5038, NewCertificates0157.C5039, NewCertificates0157.C5040, NewCertificates0157.C5041, NewCertificates0157.C5042, NewCertificates0157.C5043, NewCertificates0157.C5044, NewCertificates0157.C5045, NewCertificates0157.C5046, NewCertificates0157.C5047, NewCertificates0157.C5048, NewCertificates0157.C5049, NewCertificates0157.C5050, NewCertificates0157.C5051, NewCertificates0157.C5052, NewCertificates0157.C5053, NewCertificates0157.C5054, NewCertificates0157.C5055, NewCertificates0158.C5056, NewCertificates0158.C5057, NewCertificates0158.C5058, NewCertificates0158.C5059, NewCertificates0158.C5060, NewCertificates0158.C5061, NewCertificates0158.C5062, NewCertificates0158.C5063, NewCertificates0158.C5064, NewCertificates0158.C5065, NewCertificates0158.C5066, NewCertificates0158.C5067, NewCertificates0158.C5068, NewCertificates0158.C5069, NewCertificates0158.C5070, NewCertificates0158.C5071, NewCertificates0158.C5072, NewCertificates0158.C5073, NewCertificates0158.C5074, NewCertificates0158.C5075, NewCertificates0158.C5076, NewCertificates0158.C5077, NewCertificates0158.C5078, NewCertificates0158.C5079, NewCertificates0158.C5080, NewCertificates0158.C5081, NewCertificates0158.C5082, NewCertificates0158.C5083, NewCertificates0158.C5084, NewCertificates0158.C5085, NewCertificates0158.C5086, NewCertificates0158.C5087, NewCertificates0159.C5088, NewCertificates0159.C5089, NewCertificates0159.C5090, NewCertificates0159.C5091, NewCertificates0159.C5092, NewCertificates0159.C5093, NewCertificates0159.C5094, NewCertificates0159.C5095, NewCertificates0159.C5096, NewCertificates0159.C5097, NewCertificates0159.C5098, NewCertificates0159.C5099, NewCertificates0159.C5100, NewCertificates0159.C5101, NewCertificates0159.C5102, NewCertificates0159.C5103, NewCertificates0159.C5104, NewCertificates0159.C5105, NewCertificates0159.C5106, NewCertificates0159.C5107, NewCertificates0159.C5108, NewCertificates0159.C5109, NewCertificates0159.C5110, NewCertificates0159.C5111, NewCertificates0159.C5112, NewCertificates0159.C5113, NewCertificates0159.C5114, NewCertificates0159.C5115, NewCertificates0159.C5116, NewCertificates0159.C5117, NewCertificates0159.C5118, NewCertificates0159.C5119, NewCertificates0160.C5120, NewCertificates0160.C5121, NewCertificates0160.C5122, NewCertificates0160.C5123, NewCertificates0160.C5124, NewCertificates0160.C5125}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0, 1, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U9 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U12 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U13 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def U14 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0; 0, 1, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,6)}
def D6 : Finset (Fin 8 × Fin 8) := {(1,6), (4,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,6), (3,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5), (3,4)}
def D10 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D11 : Finset (Fin 8 × Fin 8) := {(0,6), (4,5)}
def D12 : Finset (Fin 8 × Fin 8) := {(0,6), (3,4)}
def D13 : Finset (Fin 8 × Fin 8) := {(0,6), (2,5)}
def D14 : Finset (Fin 8 × Fin 8) := {(0,6), (2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 1009672905918824512).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1009672905918824512 D i ∧ offSum 1009672905918824512 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14} := by
  decide +kernel
theorem augmentation0 : augmentation 1009672905918824512 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1009672905918824512 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 1009672905918824512 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 1009672905918824512 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 1009672905918824512 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 1009672905918824512 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 1009672905918824512 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 1009672905918824512 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 1009672905918824512 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 1009672905918824512 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 1009672905918824512 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 1009672905918824512 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 1009672905918824512 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 1009672905918824512 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 1009672905918824512 D14 = U14 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1009672905918824512 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1009672905918824512 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport108
