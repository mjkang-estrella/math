import SignedCatalogue
import NewCertificates0081
import NewCertificates0082
import NewCertificates0083
import NewCertificates0084
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport055
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 1, 2, 6, 5, 3, 4] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0081.C2602, NewCertificates0081.C2603, NewCertificates0081.C2604, NewCertificates0081.C2605, NewCertificates0081.C2606, NewCertificates0081.C2607, NewCertificates0081.C2608, NewCertificates0081.C2609, NewCertificates0081.C2610, NewCertificates0081.C2611, NewCertificates0081.C2612, NewCertificates0081.C2613, NewCertificates0081.C2614, NewCertificates0081.C2615, NewCertificates0081.C2616, NewCertificates0081.C2617, NewCertificates0081.C2618, NewCertificates0081.C2619, NewCertificates0081.C2620, NewCertificates0081.C2621, NewCertificates0081.C2622, NewCertificates0081.C2623, NewCertificates0082.C2624, NewCertificates0082.C2625, NewCertificates0082.C2626, NewCertificates0082.C2627, NewCertificates0082.C2628, NewCertificates0082.C2629, NewCertificates0082.C2630, NewCertificates0082.C2631, NewCertificates0082.C2632, NewCertificates0082.C2633, NewCertificates0082.C2634, NewCertificates0082.C2635, NewCertificates0082.C2636, NewCertificates0082.C2637, NewCertificates0082.C2638, NewCertificates0082.C2639, NewCertificates0082.C2640, NewCertificates0082.C2641, NewCertificates0082.C2642, NewCertificates0082.C2643, NewCertificates0082.C2644, NewCertificates0082.C2645, NewCertificates0082.C2646, NewCertificates0082.C2647, NewCertificates0082.C2648, NewCertificates0082.C2649, NewCertificates0082.C2650, NewCertificates0082.C2651, NewCertificates0082.C2652, NewCertificates0082.C2653, NewCertificates0082.C2654, NewCertificates0082.C2655, NewCertificates0083.C2656, NewCertificates0083.C2657, NewCertificates0083.C2658, NewCertificates0083.C2659, NewCertificates0083.C2660, NewCertificates0083.C2661, NewCertificates0083.C2662, NewCertificates0083.C2663, NewCertificates0083.C2664, NewCertificates0083.C2665, NewCertificates0083.C2666, NewCertificates0083.C2667, NewCertificates0083.C2668, NewCertificates0083.C2669, NewCertificates0083.C2670, NewCertificates0083.C2671, NewCertificates0083.C2672, NewCertificates0083.C2673, NewCertificates0083.C2674, NewCertificates0083.C2675, NewCertificates0083.C2676, NewCertificates0083.C2677, NewCertificates0083.C2678, NewCertificates0083.C2679, NewCertificates0083.C2680, NewCertificates0083.C2681, NewCertificates0083.C2682, NewCertificates0083.C2683, NewCertificates0083.C2684, NewCertificates0083.C2685, NewCertificates0083.C2686, NewCertificates0083.C2687, NewCertificates0084.C2688, NewCertificates0084.C2689, NewCertificates0084.C2690, NewCertificates0084.C2691, NewCertificates0084.C2692, NewCertificates0084.C2693, NewCertificates0084.C2694, NewCertificates0084.C2695, NewCertificates0084.C2696, NewCertificates0084.C2697, NewCertificates0084.C2698, NewCertificates0084.C2699, NewCertificates0084.C2700, NewCertificates0084.C2701}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U9 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U10 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U11 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def U12 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D2 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,6)}
def D4 : Finset (Fin 8 × Fin 8) := {(3,6), (4,5)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D7 : Finset (Fin 8 × Fin 8) := {(2,5), (3,6)}
def D8 : Finset (Fin 8 × Fin 8) := {(1,6)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,6), (3,4)}
def D10 : Finset (Fin 8 × Fin 8) := {(1,6), (4,5)}
def D11 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5)}
def D12 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 507240071416561792).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 507240071416561792 D i ∧ offSum 507240071416561792 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12} := by
  decide +kernel
theorem augmentation0 : augmentation 507240071416561792 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 507240071416561792 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 507240071416561792 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 507240071416561792 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 507240071416561792 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 507240071416561792 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 507240071416561792 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 507240071416561792 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 507240071416561792 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 507240071416561792 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 507240071416561792 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 507240071416561792 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 507240071416561792 D12 = U12 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 507240071416561792 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 507240071416561792 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport055
