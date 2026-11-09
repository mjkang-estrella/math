import SignedCatalogue
import NewCertificates0085
import NewCertificates0086
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport057
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0085.C2734, NewCertificates0085.C2735, NewCertificates0085.C2736, NewCertificates0085.C2737, NewCertificates0085.C2738, NewCertificates0085.C2739, NewCertificates0085.C2740, NewCertificates0085.C2741, NewCertificates0085.C2742, NewCertificates0085.C2743, NewCertificates0085.C2744, NewCertificates0085.C2745, NewCertificates0085.C2746, NewCertificates0085.C2747, NewCertificates0085.C2748, NewCertificates0085.C2749, NewCertificates0085.C2750, NewCertificates0085.C2751, NewCertificates0086.C2752, NewCertificates0086.C2753, NewCertificates0086.C2754, NewCertificates0086.C2755, NewCertificates0086.C2756, NewCertificates0086.C2757, NewCertificates0086.C2758, NewCertificates0086.C2759, NewCertificates0086.C2760, NewCertificates0086.C2761, NewCertificates0086.C2762, NewCertificates0086.C2763, NewCertificates0086.C2764, NewCertificates0086.C2765}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 1, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 511752742551732352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 511752742551732352 D i ∧ offSum 511752742551732352 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 511752742551732352 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 511752742551732352 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 511752742551732352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport057
