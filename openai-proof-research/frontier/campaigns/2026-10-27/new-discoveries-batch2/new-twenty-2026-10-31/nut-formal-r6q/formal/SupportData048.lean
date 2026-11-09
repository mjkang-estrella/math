import SignedCatalogue
import NewCertificates0072
import NewCertificates0073
import NewCertificates0074
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport048
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 4, 3, 5, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 3, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0072.C2330, NewCertificates0072.C2331, NewCertificates0072.C2332, NewCertificates0072.C2333, NewCertificates0072.C2334, NewCertificates0072.C2335, NewCertificates0073.C2336, NewCertificates0073.C2337, NewCertificates0073.C2338, NewCertificates0073.C2339, NewCertificates0073.C2340, NewCertificates0073.C2341, NewCertificates0073.C2342, NewCertificates0073.C2343, NewCertificates0073.C2344, NewCertificates0073.C2345, NewCertificates0073.C2346, NewCertificates0073.C2347, NewCertificates0073.C2348, NewCertificates0073.C2349, NewCertificates0073.C2350, NewCertificates0073.C2351, NewCertificates0073.C2352, NewCertificates0073.C2353, NewCertificates0073.C2354, NewCertificates0073.C2355, NewCertificates0073.C2356, NewCertificates0073.C2357, NewCertificates0073.C2358, NewCertificates0073.C2359, NewCertificates0073.C2360, NewCertificates0073.C2361, NewCertificates0073.C2362, NewCertificates0073.C2363, NewCertificates0073.C2364, NewCertificates0073.C2365, NewCertificates0073.C2366, NewCertificates0073.C2367, NewCertificates0074.C2368, NewCertificates0074.C2369, NewCertificates0074.C2370, NewCertificates0074.C2371, NewCertificates0074.C2372, NewCertificates0074.C2373, NewCertificates0074.C2374, NewCertificates0074.C2375, NewCertificates0074.C2376, NewCertificates0074.C2377}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 1, 0, 0, 0, 1; 0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 2, 0, 0, 0, 1; 0, 0, 2, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 1, 0, 0, 1, 1, 0, 0; 1, 0, 1, 0, 1, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(2,3)}
theorem doubled_enumeration : ((supportEdges 1527380943340847232).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 1527380943340847232 D i ∧ offSum 1527380943340847232 D i ≤ 3) = {D0, D1} := by
  decide +kernel
theorem augmentation0 : augmentation 1527380943340847232 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 1527380943340847232 D1 = U1 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 1527380943340847232 = {U0, U1} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 1527380943340847232 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport048
