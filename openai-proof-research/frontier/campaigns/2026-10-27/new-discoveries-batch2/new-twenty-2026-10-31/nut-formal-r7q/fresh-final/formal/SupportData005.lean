import SignedCatalogue
import NewCertificates0007
import NewCertificates0008
import NewCertificates0009
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport005
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 5, 4, 6, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 4, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0007.C224, NewCertificates0007.C225, NewCertificates0007.C226, NewCertificates0007.C227, NewCertificates0007.C228, NewCertificates0007.C229, NewCertificates0007.C230, NewCertificates0007.C231, NewCertificates0007.C232, NewCertificates0007.C233, NewCertificates0007.C234, NewCertificates0007.C235, NewCertificates0007.C236, NewCertificates0007.C237, NewCertificates0007.C238, NewCertificates0007.C239, NewCertificates0007.C240, NewCertificates0007.C241, NewCertificates0007.C242, NewCertificates0007.C243, NewCertificates0007.C244, NewCertificates0007.C245, NewCertificates0007.C246, NewCertificates0007.C247, NewCertificates0007.C248, NewCertificates0007.C249, NewCertificates0007.C250, NewCertificates0007.C251, NewCertificates0007.C252, NewCertificates0007.C253, NewCertificates0007.C254, NewCertificates0007.C255, NewCertificates0008.C256, NewCertificates0008.C257, NewCertificates0008.C258, NewCertificates0008.C259, NewCertificates0008.C260, NewCertificates0008.C261, NewCertificates0008.C262, NewCertificates0008.C263, NewCertificates0008.C264, NewCertificates0008.C265, NewCertificates0008.C266, NewCertificates0008.C267, NewCertificates0008.C268, NewCertificates0008.C269, NewCertificates0008.C270, NewCertificates0008.C271, NewCertificates0008.C272, NewCertificates0008.C273, NewCertificates0008.C274, NewCertificates0008.C275, NewCertificates0008.C276, NewCertificates0008.C277, NewCertificates0008.C278, NewCertificates0008.C279, NewCertificates0008.C280, NewCertificates0008.C281, NewCertificates0008.C282, NewCertificates0008.C283, NewCertificates0008.C284, NewCertificates0008.C285, NewCertificates0008.C286, NewCertificates0008.C287, NewCertificates0009.C288, NewCertificates0009.C289, NewCertificates0009.C290, NewCertificates0009.C291, NewCertificates0009.C292, NewCertificates0009.C293, NewCertificates0009.C294, NewCertificates0009.C295, NewCertificates0009.C296, NewCertificates0009.C297, NewCertificates0009.C298, NewCertificates0009.C299, NewCertificates0009.C300, NewCertificates0009.C301, NewCertificates0009.C302, NewCertificates0009.C303, NewCertificates0009.C304, NewCertificates0009.C305, NewCertificates0009.C306, NewCertificates0009.C307, NewCertificates0009.C308, NewCertificates0009.C309, NewCertificates0009.C310, NewCertificates0009.C311, NewCertificates0009.C312, NewCertificates0009.C313, NewCertificates0009.C314, NewCertificates0009.C315, NewCertificates0009.C316, NewCertificates0009.C317, NewCertificates0009.C318, NewCertificates0009.C319}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 0, 0, 1, 2, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 2, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 0, 1, 2, 0; 0, 0, 0, 2, 1, 0, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,6)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,6)}
def D3 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(2,6), (4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(2,6), (3,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(3,5), (4,6)}
theorem doubled_enumeration : ((supportEdges 798289837235929216).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 798289837235929216 D i ∧ offSum 798289837235929216 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7} := by
  decide +kernel
theorem augmentation0 : augmentation 798289837235929216 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 798289837235929216 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 798289837235929216 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 798289837235929216 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 798289837235929216 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 798289837235929216 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 798289837235929216 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 798289837235929216 D7 = U7 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 798289837235929216 = {U0, U1, U2, U3, U4, U5, U6, U7} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 798289837235929216 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport005
