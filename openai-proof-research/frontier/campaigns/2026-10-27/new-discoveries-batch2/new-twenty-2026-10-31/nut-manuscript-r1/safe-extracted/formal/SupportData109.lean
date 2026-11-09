import SignedCatalogue
import NewCertificates0160
import NewCertificates0161
import NewCertificates0162
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport109
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 3, 7, 4, 5, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0160.C5126, NewCertificates0160.C5127, NewCertificates0160.C5128, NewCertificates0160.C5129, NewCertificates0160.C5130, NewCertificates0160.C5131, NewCertificates0160.C5132, NewCertificates0160.C5133, NewCertificates0160.C5134, NewCertificates0160.C5135, NewCertificates0160.C5136, NewCertificates0160.C5137, NewCertificates0160.C5138, NewCertificates0160.C5139, NewCertificates0160.C5140, NewCertificates0160.C5141, NewCertificates0160.C5142, NewCertificates0160.C5143, NewCertificates0160.C5144, NewCertificates0160.C5145, NewCertificates0160.C5146, NewCertificates0160.C5147, NewCertificates0160.C5148, NewCertificates0160.C5149, NewCertificates0160.C5150, NewCertificates0160.C5151, NewCertificates0161.C5152, NewCertificates0161.C5153, NewCertificates0161.C5154, NewCertificates0161.C5155, NewCertificates0161.C5156, NewCertificates0161.C5157, NewCertificates0161.C5158, NewCertificates0161.C5159, NewCertificates0161.C5160, NewCertificates0161.C5161, NewCertificates0161.C5162, NewCertificates0161.C5163, NewCertificates0161.C5164, NewCertificates0161.C5165, NewCertificates0161.C5166, NewCertificates0161.C5167, NewCertificates0161.C5168, NewCertificates0161.C5169, NewCertificates0161.C5170, NewCertificates0161.C5171, NewCertificates0161.C5172, NewCertificates0161.C5173, NewCertificates0161.C5174, NewCertificates0161.C5175, NewCertificates0161.C5176, NewCertificates0161.C5177, NewCertificates0161.C5178, NewCertificates0161.C5179, NewCertificates0161.C5180, NewCertificates0161.C5181, NewCertificates0161.C5182, NewCertificates0161.C5183, NewCertificates0162.C5184, NewCertificates0162.C5185, NewCertificates0162.C5186, NewCertificates0162.C5187, NewCertificates0162.C5188, NewCertificates0162.C5189, NewCertificates0162.C5190, NewCertificates0162.C5191, NewCertificates0162.C5192, NewCertificates0162.C5193, NewCertificates0162.C5194, NewCertificates0162.C5195, NewCertificates0162.C5196, NewCertificates0162.C5197, NewCertificates0162.C5198, NewCertificates0162.C5199, NewCertificates0162.C5200, NewCertificates0162.C5201, NewCertificates0162.C5202, NewCertificates0162.C5203, NewCertificates0162.C5204, NewCertificates0162.C5205, NewCertificates0162.C5206, NewCertificates0162.C5207, NewCertificates0162.C5208, NewCertificates0162.C5209, NewCertificates0162.C5210, NewCertificates0162.C5211, NewCertificates0162.C5212, NewCertificates0162.C5213, NewCertificates0162.C5214, NewCertificates0162.C5215}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 1, 0, 0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U8 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U9 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1, 0, 1; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 2, 0; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 2, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 2, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(3,6)}
def D5 : Finset (Fin 8 × Fin 8) := {(1,5), (3,6)}
def D6 : Finset (Fin 8 × Fin 8) := {(2,4), (3,6)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4), (3,6)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D9 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5)}
def D10 : Finset (Fin 8 × Fin 8) := {(0,6), (2,4)}
def D11 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (2,4)}
theorem doubled_enumeration : ((supportEdges 4037902047583936576).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4037902047583936576 D i ∧ offSum 4037902047583936576 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11} := by
  decide +kernel
theorem augmentation0 : augmentation 4037902047583936576 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4037902047583936576 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4037902047583936576 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4037902047583936576 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 4037902047583936576 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 4037902047583936576 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 4037902047583936576 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 4037902047583936576 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 4037902047583936576 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 4037902047583936576 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 4037902047583936576 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 4037902047583936576 D11 = U11 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4037902047583936576 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4037902047583936576 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport109
