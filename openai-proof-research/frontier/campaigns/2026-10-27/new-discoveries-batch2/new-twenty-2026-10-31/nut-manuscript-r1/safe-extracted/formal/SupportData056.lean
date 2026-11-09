import SignedCatalogue
import NewCertificates0084
import NewCertificates0085
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport056
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0084.C2702, NewCertificates0084.C2703, NewCertificates0084.C2704, NewCertificates0084.C2705, NewCertificates0084.C2706, NewCertificates0084.C2707, NewCertificates0084.C2708, NewCertificates0084.C2709, NewCertificates0084.C2710, NewCertificates0084.C2711, NewCertificates0084.C2712, NewCertificates0084.C2713, NewCertificates0084.C2714, NewCertificates0084.C2715, NewCertificates0084.C2716, NewCertificates0084.C2717, NewCertificates0084.C2718, NewCertificates0084.C2719, NewCertificates0085.C2720, NewCertificates0085.C2721, NewCertificates0085.C2722, NewCertificates0085.C2723, NewCertificates0085.C2724, NewCertificates0085.C2725, NewCertificates0085.C2726, NewCertificates0085.C2727, NewCertificates0085.C2728, NewCertificates0085.C2729, NewCertificates0085.C2730, NewCertificates0085.C2731, NewCertificates0085.C2732, NewCertificates0085.C2733}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 516317639415480448).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 516317639415480448 D i ∧ offSum 516317639415480448 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 516317639415480448 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 516317639415480448 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 516317639415480448 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 516317639415480448 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport056
