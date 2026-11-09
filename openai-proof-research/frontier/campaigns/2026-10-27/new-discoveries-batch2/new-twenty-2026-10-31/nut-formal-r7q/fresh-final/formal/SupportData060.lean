import SignedCatalogue
import NewCertificates0088
import NewCertificates0089
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport060
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 6, 4, 5, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0088.C2830, NewCertificates0088.C2831, NewCertificates0088.C2832, NewCertificates0088.C2833, NewCertificates0088.C2834, NewCertificates0088.C2835, NewCertificates0088.C2836, NewCertificates0088.C2837, NewCertificates0088.C2838, NewCertificates0088.C2839, NewCertificates0088.C2840, NewCertificates0088.C2841, NewCertificates0088.C2842, NewCertificates0088.C2843, NewCertificates0088.C2844, NewCertificates0088.C2845, NewCertificates0088.C2846, NewCertificates0088.C2847, NewCertificates0089.C2848, NewCertificates0089.C2849, NewCertificates0089.C2850, NewCertificates0089.C2851, NewCertificates0089.C2852, NewCertificates0089.C2853, NewCertificates0089.C2854, NewCertificates0089.C2855, NewCertificates0089.C2856, NewCertificates0089.C2857, NewCertificates0089.C2858, NewCertificates0089.C2859, NewCertificates0089.C2860, NewCertificates0089.C2861}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 1, 0, 1, 0, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 798857219866148992).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 798857219866148992 D i ∧ offSum 798857219866148992 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 798857219866148992 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 798857219866148992 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 798857219866148992 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport060
