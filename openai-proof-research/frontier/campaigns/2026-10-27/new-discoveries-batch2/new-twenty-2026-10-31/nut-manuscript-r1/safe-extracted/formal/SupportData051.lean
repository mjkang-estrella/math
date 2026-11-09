import SignedCatalogue
import NewCertificates0077
import NewCertificates0078
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport051
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 6, 3, 5, 1, 2] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0077.C2474, NewCertificates0077.C2475, NewCertificates0077.C2476, NewCertificates0077.C2477, NewCertificates0077.C2478, NewCertificates0077.C2479, NewCertificates0077.C2480, NewCertificates0077.C2481, NewCertificates0077.C2482, NewCertificates0077.C2483, NewCertificates0077.C2484, NewCertificates0077.C2485, NewCertificates0077.C2486, NewCertificates0077.C2487, NewCertificates0077.C2488, NewCertificates0077.C2489, NewCertificates0077.C2490, NewCertificates0077.C2491, NewCertificates0077.C2492, NewCertificates0077.C2493, NewCertificates0077.C2494, NewCertificates0077.C2495, NewCertificates0078.C2496, NewCertificates0078.C2497, NewCertificates0078.C2498, NewCertificates0078.C2499, NewCertificates0078.C2500, NewCertificates0078.C2501, NewCertificates0078.C2502, NewCertificates0078.C2503, NewCertificates0078.C2504, NewCertificates0078.C2505, NewCertificates0078.C2506, NewCertificates0078.C2507, NewCertificates0078.C2508, NewCertificates0078.C2509, NewCertificates0078.C2510, NewCertificates0078.C2511, NewCertificates0078.C2512, NewCertificates0078.C2513, NewCertificates0078.C2514, NewCertificates0078.C2515, NewCertificates0078.C2516, NewCertificates0078.C2517, NewCertificates0078.C2518, NewCertificates0078.C2519, NewCertificates0078.C2520, NewCertificates0078.C2521}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 1, 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 5882357144168710272).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5882357144168710272 D i ∧ offSum 5882357144168710272 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 5882357144168710272 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5882357144168710272 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5882357144168710272 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5882357144168710272 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport051
