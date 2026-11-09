import SignedCatalogue
import NewCertificates0079
import NewCertificates0080
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport053
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 4, 5, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0079.C2554, NewCertificates0079.C2555, NewCertificates0079.C2556, NewCertificates0079.C2557, NewCertificates0079.C2558, NewCertificates0079.C2559, NewCertificates0080.C2560, NewCertificates0080.C2561, NewCertificates0080.C2562, NewCertificates0080.C2563, NewCertificates0080.C2564, NewCertificates0080.C2565, NewCertificates0080.C2566, NewCertificates0080.C2567, NewCertificates0080.C2568, NewCertificates0080.C2569, NewCertificates0080.C2570, NewCertificates0080.C2571, NewCertificates0080.C2572, NewCertificates0080.C2573, NewCertificates0080.C2574, NewCertificates0080.C2575, NewCertificates0080.C2576, NewCertificates0080.C2577, NewCertificates0080.C2578, NewCertificates0080.C2579, NewCertificates0080.C2580, NewCertificates0080.C2581, NewCertificates0080.C2582, NewCertificates0080.C2583, NewCertificates0080.C2584, NewCertificates0080.C2585}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
theorem doubled_enumeration : ((supportEdges 515196137020375168).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 515196137020375168 D i ∧ offSum 515196137020375168 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 515196137020375168 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 515196137020375168 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 515196137020375168 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 515196137020375168 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport053
