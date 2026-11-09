import SignedCatalogue
import NewCertificates0029
import NewCertificates0030
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport020
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 4, 5, 6, 3, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 3, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0029.C936, NewCertificates0029.C937, NewCertificates0029.C938, NewCertificates0029.C939, NewCertificates0029.C940, NewCertificates0029.C941, NewCertificates0029.C942, NewCertificates0029.C943, NewCertificates0029.C944, NewCertificates0029.C945, NewCertificates0029.C946, NewCertificates0029.C947, NewCertificates0029.C948, NewCertificates0029.C949, NewCertificates0029.C950, NewCertificates0029.C951, NewCertificates0029.C952, NewCertificates0029.C953, NewCertificates0029.C954, NewCertificates0029.C955, NewCertificates0029.C956, NewCertificates0029.C957, NewCertificates0029.C958, NewCertificates0029.C959, NewCertificates0030.C960, NewCertificates0030.C961, NewCertificates0030.C962, NewCertificates0030.C963, NewCertificates0030.C964, NewCertificates0030.C965, NewCertificates0030.C966, NewCertificates0030.C967, NewCertificates0030.C968, NewCertificates0030.C969, NewCertificates0030.C970, NewCertificates0030.C971, NewCertificates0030.C972, NewCertificates0030.C973, NewCertificates0030.C974, NewCertificates0030.C975, NewCertificates0030.C976, NewCertificates0030.C977, NewCertificates0030.C978, NewCertificates0030.C979, NewCertificates0030.C980, NewCertificates0030.C981, NewCertificates0030.C982, NewCertificates0030.C983}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 1, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 0, 1; 0, 0, 0, 2, 0, 0, 1, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 1, 1, 0, 0; 1, 1, 0, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1383828705214234752).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1383828705214234752 D i ∧ offSum 1383828705214234752 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1383828705214234752 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1383828705214234752 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1383828705214234752 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1383828705214234752 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport020
