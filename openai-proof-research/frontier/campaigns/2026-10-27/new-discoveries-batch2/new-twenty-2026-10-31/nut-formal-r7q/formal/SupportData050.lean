import SignedCatalogue
import NewCertificates0075
import NewCertificates0076
import NewCertificates0077
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport050
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 4, 5, 3, 6, 2, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 2, 3, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0075.C2426, NewCertificates0075.C2427, NewCertificates0075.C2428, NewCertificates0075.C2429, NewCertificates0075.C2430, NewCertificates0075.C2431, NewCertificates0076.C2432, NewCertificates0076.C2433, NewCertificates0076.C2434, NewCertificates0076.C2435, NewCertificates0076.C2436, NewCertificates0076.C2437, NewCertificates0076.C2438, NewCertificates0076.C2439, NewCertificates0076.C2440, NewCertificates0076.C2441, NewCertificates0076.C2442, NewCertificates0076.C2443, NewCertificates0076.C2444, NewCertificates0076.C2445, NewCertificates0076.C2446, NewCertificates0076.C2447, NewCertificates0076.C2448, NewCertificates0076.C2449, NewCertificates0076.C2450, NewCertificates0076.C2451, NewCertificates0076.C2452, NewCertificates0076.C2453, NewCertificates0076.C2454, NewCertificates0076.C2455, NewCertificates0076.C2456, NewCertificates0076.C2457, NewCertificates0076.C2458, NewCertificates0076.C2459, NewCertificates0076.C2460, NewCertificates0076.C2461, NewCertificates0076.C2462, NewCertificates0076.C2463, NewCertificates0077.C2464, NewCertificates0077.C2465, NewCertificates0077.C2466, NewCertificates0077.C2467, NewCertificates0077.C2468, NewCertificates0077.C2469, NewCertificates0077.C2470, NewCertificates0077.C2471, NewCertificates0077.C2472, NewCertificates0077.C2473}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0, 1, 1; 0, 0, 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 0, 0, 1, 1, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 3545112220304687232).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 3545112220304687232 D i ∧ offSum 3545112220304687232 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 3545112220304687232 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 3545112220304687232 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 3545112220304687232 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 3545112220304687232 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport050
