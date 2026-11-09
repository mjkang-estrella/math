import SignedCatalogue
import NewCertificates0078
import NewCertificates0079
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport052
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 3, 5, 4, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0078.C2522, NewCertificates0078.C2523, NewCertificates0078.C2524, NewCertificates0078.C2525, NewCertificates0078.C2526, NewCertificates0078.C2527, NewCertificates0079.C2528, NewCertificates0079.C2529, NewCertificates0079.C2530, NewCertificates0079.C2531, NewCertificates0079.C2532, NewCertificates0079.C2533, NewCertificates0079.C2534, NewCertificates0079.C2535, NewCertificates0079.C2536, NewCertificates0079.C2537, NewCertificates0079.C2538, NewCertificates0079.C2539, NewCertificates0079.C2540, NewCertificates0079.C2541, NewCertificates0079.C2542, NewCertificates0079.C2543, NewCertificates0079.C2544, NewCertificates0079.C2545, NewCertificates0079.C2546, NewCertificates0079.C2547, NewCertificates0079.C2548, NewCertificates0079.C2549, NewCertificates0079.C2550, NewCertificates0079.C2551, NewCertificates0079.C2552, NewCertificates0079.C2553}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 1, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
theorem doubled_enumeration : ((supportEdges 950915279475982464).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 950915279475982464 D i ∧ offSum 950915279475982464 D i ≤ 3) = {D0} := by
  decide +kernel
theorem augmentation0 : augmentation 950915279475982464 D0 = U0 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 950915279475982464 = {U0} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 950915279475982464 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport052
