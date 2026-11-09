import SignedCatalogue
import NewCertificates0087
import NewCertificates0088
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport059
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 5, 6, 2, 4, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0087.C2798, NewCertificates0087.C2799, NewCertificates0087.C2800, NewCertificates0087.C2801, NewCertificates0087.C2802, NewCertificates0087.C2803, NewCertificates0087.C2804, NewCertificates0087.C2805, NewCertificates0087.C2806, NewCertificates0087.C2807, NewCertificates0087.C2808, NewCertificates0087.C2809, NewCertificates0087.C2810, NewCertificates0087.C2811, NewCertificates0087.C2812, NewCertificates0087.C2813, NewCertificates0087.C2814, NewCertificates0087.C2815, NewCertificates0088.C2816, NewCertificates0088.C2817, NewCertificates0088.C2818, NewCertificates0088.C2819, NewCertificates0088.C2820, NewCertificates0088.C2821, NewCertificates0088.C2822, NewCertificates0088.C2823, NewCertificates0088.C2824, NewCertificates0088.C2825, NewCertificates0088.C2826, NewCertificates0088.C2827, NewCertificates0088.C2828, NewCertificates0088.C2829}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 2526119341869547648).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 2526119341869547648 D i ∧ offSum 2526119341869547648 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 2526119341869547648 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 2526119341869547648 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 2526119341869547648 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 2526119341869547648 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport059
