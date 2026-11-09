import SignedCatalogue
import NewCertificates0092
import NewCertificates0093
import NewCertificates0094
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport064
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 6, 4, 5, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 4, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0092.C2974, NewCertificates0092.C2975, NewCertificates0093.C2976, NewCertificates0093.C2977, NewCertificates0093.C2978, NewCertificates0093.C2979, NewCertificates0093.C2980, NewCertificates0093.C2981, NewCertificates0093.C2982, NewCertificates0093.C2983, NewCertificates0093.C2984, NewCertificates0093.C2985, NewCertificates0093.C2986, NewCertificates0093.C2987, NewCertificates0093.C2988, NewCertificates0093.C2989, NewCertificates0093.C2990, NewCertificates0093.C2991, NewCertificates0093.C2992, NewCertificates0093.C2993, NewCertificates0093.C2994, NewCertificates0093.C2995, NewCertificates0093.C2996, NewCertificates0093.C2997, NewCertificates0093.C2998, NewCertificates0093.C2999, NewCertificates0093.C3000, NewCertificates0093.C3001, NewCertificates0093.C3002, NewCertificates0093.C3003, NewCertificates0093.C3004, NewCertificates0093.C3005, NewCertificates0093.C3006, NewCertificates0093.C3007, NewCertificates0094.C3008, NewCertificates0094.C3009, NewCertificates0094.C3010, NewCertificates0094.C3011, NewCertificates0094.C3012, NewCertificates0094.C3013}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 1, 1, 1, 0; 0, 2, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 1, 0; 0, 1, 0, 0, 2, 0, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,5)}
theorem doubled_enumeration : ((supportEdges 944650228600938624).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 944650228600938624 D i ∧ offSum 944650228600938624 D i ≤ 3) = {D0, D1, D2} := by
  decide +kernel
theorem augmentation0 : augmentation 944650228600938624 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 944650228600938624 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 944650228600938624 D2 = U2 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 944650228600938624 = {U0, U1, U2} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 944650228600938624 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport064
