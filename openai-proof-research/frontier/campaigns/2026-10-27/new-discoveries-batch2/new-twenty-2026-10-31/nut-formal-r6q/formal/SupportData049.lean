import SignedCatalogue
import NewCertificates0074
import NewCertificates0075
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport049
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 6, 5, 1, 2, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 4]
def matrices : Finset QuotientMatrix := {NewCertificates0074.C2378, NewCertificates0074.C2379, NewCertificates0074.C2380, NewCertificates0074.C2381, NewCertificates0074.C2382, NewCertificates0074.C2383, NewCertificates0074.C2384, NewCertificates0074.C2385, NewCertificates0074.C2386, NewCertificates0074.C2387, NewCertificates0074.C2388, NewCertificates0074.C2389, NewCertificates0074.C2390, NewCertificates0074.C2391, NewCertificates0074.C2392, NewCertificates0074.C2393, NewCertificates0074.C2394, NewCertificates0074.C2395, NewCertificates0074.C2396, NewCertificates0074.C2397, NewCertificates0074.C2398, NewCertificates0074.C2399, NewCertificates0075.C2400, NewCertificates0075.C2401, NewCertificates0075.C2402, NewCertificates0075.C2403, NewCertificates0075.C2404, NewCertificates0075.C2405, NewCertificates0075.C2406, NewCertificates0075.C2407, NewCertificates0075.C2408, NewCertificates0075.C2409, NewCertificates0075.C2410, NewCertificates0075.C2411, NewCertificates0075.C2412, NewCertificates0075.C2413, NewCertificates0075.C2414, NewCertificates0075.C2415, NewCertificates0075.C2416, NewCertificates0075.C2417, NewCertificates0075.C2418, NewCertificates0075.C2419, NewCertificates0075.C2420, NewCertificates0075.C2421, NewCertificates0075.C2422, NewCertificates0075.C2423, NewCertificates0075.C2424, NewCertificates0075.C2425}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 0, 1, 0, 0, 1; 1, 0, 0, 0, 1, 0, 1, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 5877792212676788352).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 5877792212676788352 D i ∧ offSum 5877792212676788352 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 5877792212676788352 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 5877792212676788352 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 5877792212676788352 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 5877792212676788352 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport049
