import SignedCatalogue
import NewCertificates0086
import NewCertificates0087
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport058
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 3, 6, 4, 2, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0086.C2766, NewCertificates0086.C2767, NewCertificates0086.C2768, NewCertificates0086.C2769, NewCertificates0086.C2770, NewCertificates0086.C2771, NewCertificates0086.C2772, NewCertificates0086.C2773, NewCertificates0086.C2774, NewCertificates0086.C2775, NewCertificates0086.C2776, NewCertificates0086.C2777, NewCertificates0086.C2778, NewCertificates0086.C2779, NewCertificates0086.C2780, NewCertificates0086.C2781, NewCertificates0086.C2782, NewCertificates0086.C2783, NewCertificates0087.C2784, NewCertificates0087.C2785, NewCertificates0087.C2786, NewCertificates0087.C2787, NewCertificates0087.C2788, NewCertificates0087.C2789, NewCertificates0087.C2790, NewCertificates0087.C2791, NewCertificates0087.C2792, NewCertificates0087.C2793, NewCertificates0087.C2794, NewCertificates0087.C2795, NewCertificates0087.C2796, NewCertificates0087.C2797}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 1, 1, 0, 0, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 2, 0, 0, 1; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 0, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 803422116729897088).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 803422116729897088 D i ∧ offSum 803422116729897088 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 803422116729897088 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 803422116729897088 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 803422116729897088 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 803422116729897088 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport058
