import SignedCatalogue
import NewCertificates0226
import NewCertificates0227
import NewCertificates0228
import NewCertificates0229
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport154
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 5, 7, 4, 1, 6, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 2, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0226.C7260, NewCertificates0226.C7261, NewCertificates0226.C7262, NewCertificates0226.C7263, NewCertificates0227.C7264, NewCertificates0227.C7265, NewCertificates0227.C7266, NewCertificates0227.C7267, NewCertificates0227.C7268, NewCertificates0227.C7269, NewCertificates0227.C7270, NewCertificates0227.C7271, NewCertificates0227.C7272, NewCertificates0227.C7273, NewCertificates0227.C7274, NewCertificates0227.C7275, NewCertificates0227.C7276, NewCertificates0227.C7277, NewCertificates0227.C7278, NewCertificates0227.C7279, NewCertificates0227.C7280, NewCertificates0227.C7281, NewCertificates0227.C7282, NewCertificates0227.C7283, NewCertificates0227.C7284, NewCertificates0227.C7285, NewCertificates0227.C7286, NewCertificates0227.C7287, NewCertificates0227.C7288, NewCertificates0227.C7289, NewCertificates0227.C7290, NewCertificates0227.C7291, NewCertificates0227.C7292, NewCertificates0227.C7293, NewCertificates0227.C7294, NewCertificates0227.C7295, NewCertificates0228.C7296, NewCertificates0228.C7297, NewCertificates0228.C7298, NewCertificates0228.C7299, NewCertificates0228.C7300, NewCertificates0228.C7301, NewCertificates0228.C7302, NewCertificates0228.C7303, NewCertificates0228.C7304, NewCertificates0228.C7305, NewCertificates0228.C7306, NewCertificates0228.C7307, NewCertificates0228.C7308, NewCertificates0228.C7309, NewCertificates0228.C7310, NewCertificates0228.C7311, NewCertificates0228.C7312, NewCertificates0228.C7313, NewCertificates0228.C7314, NewCertificates0228.C7315, NewCertificates0228.C7316, NewCertificates0228.C7317, NewCertificates0228.C7318, NewCertificates0228.C7319, NewCertificates0228.C7320, NewCertificates0228.C7321, NewCertificates0228.C7322, NewCertificates0228.C7323, NewCertificates0228.C7324, NewCertificates0228.C7325, NewCertificates0228.C7326, NewCertificates0228.C7327, NewCertificates0229.C7328, NewCertificates0229.C7329, NewCertificates0229.C7330, NewCertificates0229.C7331, NewCertificates0229.C7332, NewCertificates0229.C7333, NewCertificates0229.C7334, NewCertificates0229.C7335}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 1, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 2, 0, 0; 1, 0, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U6 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U7 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 1, 0, 0, 1, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U8 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def U9 : QuotientMatrix := !![0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 0, 1, 0; 0, 2, 0, 0, 0, 1, 0, 0; 2, 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
def D2 : Finset (Fin 8 × Fin 8) := {(1,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,4), (2,3)}
def D4 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,3), (4,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(0,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(0,5), (2,3)}
def D8 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4)}
def D9 : Finset (Fin 8 × Fin 8) := {(0,5), (1,4), (2,3)}
theorem doubled_enumeration : ((supportEdges 4867284136152830112).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 4867284136152830112 D i ∧ offSum 4867284136152830112 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9} := by
  decide +kernel
theorem augmentation0 : augmentation 4867284136152830112 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 4867284136152830112 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 4867284136152830112 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 4867284136152830112 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 4867284136152830112 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 4867284136152830112 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 4867284136152830112 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 4867284136152830112 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 4867284136152830112 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 4867284136152830112 D9 = U9 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 4867284136152830112 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 4867284136152830112 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport154
