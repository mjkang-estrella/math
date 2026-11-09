import SignedCatalogue
import NewCertificates0091
import NewCertificates0092
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport063
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 6, 2, 3, 5] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0091.C2942, NewCertificates0091.C2943, NewCertificates0092.C2944, NewCertificates0092.C2945, NewCertificates0092.C2946, NewCertificates0092.C2947, NewCertificates0092.C2948, NewCertificates0092.C2949, NewCertificates0092.C2950, NewCertificates0092.C2951, NewCertificates0092.C2952, NewCertificates0092.C2953, NewCertificates0092.C2954, NewCertificates0092.C2955, NewCertificates0092.C2956, NewCertificates0092.C2957, NewCertificates0092.C2958, NewCertificates0092.C2959, NewCertificates0092.C2960, NewCertificates0092.C2961, NewCertificates0092.C2962, NewCertificates0092.C2963, NewCertificates0092.C2964, NewCertificates0092.C2965, NewCertificates0092.C2966, NewCertificates0092.C2967, NewCertificates0092.C2968, NewCertificates0092.C2969, NewCertificates0092.C2970, NewCertificates0092.C2971, NewCertificates0092.C2972, NewCertificates0092.C2973}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 1, 1, 0, 0; 0, 0, 0, 0, 1, 1, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 1381000401803853952).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1381000401803853952 D i ∧ offSum 1381000401803853952 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 1381000401803853952 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1381000401803853952 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1381000401803853952 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport063
