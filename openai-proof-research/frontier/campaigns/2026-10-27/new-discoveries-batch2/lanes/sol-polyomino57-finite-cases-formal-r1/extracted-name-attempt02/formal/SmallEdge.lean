import SmallData
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Polyomino57.Diagonal.FiniteProof.Small
open Polyomino57
theorem edge_row0 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 0) (point w) → value A 0 ≤ value A w + 1 := by decide
theorem edge_row1 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 1) (point w) → value A 1 ≤ value A w + 1 := by decide
theorem edge_row2 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 2) (point w) → value A 2 ≤ value A w + 1 := by decide
theorem edge_row3 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 3) (point w) → value A 3 ≤ value A w + 1 := by decide
theorem edge_row4 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 4) (point w) → value A 4 ≤ value A w + 1 := by decide
theorem edge_row5 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 5) (point w) → value A 5 ≤ value A w + 1 := by decide
theorem edge_row6 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 6) (point w) → value A 6 ≤ value A w + 1 := by decide
theorem edge_row7 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 7) (point w) → value A 7 ≤ value A w + 1 := by decide
theorem edge_row8 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 8) (point w) → value A 8 ≤ value A w + 1 := by decide
theorem edge_row9 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 9) (point w) → value A 9 ≤ value A w + 1 := by decide
theorem edge_row10 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 10) (point w) → value A 10 ≤ value A w + 1 := by decide
theorem edge_row11 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 11) (point w) → value A 11 ≤ value A w + 1 := by decide
theorem edge_row12 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 12) (point w) → value A 12 ≤ value A w + 1 := by decide
theorem edge_row13 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 13) (point w) → value A 13 ≤ value A w + 1 := by decide
theorem edge_row14 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 14) (point w) → value A 14 ≤ value A w + 1 := by decide
theorem edge_row15 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 15) (point w) → value A 15 ≤ value A w + 1 := by decide
theorem edge_row16 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 16) (point w) → value A 16 ≤ value A w + 1 := by decide
theorem edge_row17 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 17) (point w) → value A 17 ≤ value A w + 1 := by decide
theorem edge_row18 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 18) (point w) → value A 18 ≤ value A w + 1 := by decide
theorem edge_row19 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 19) (point w) → value A 19 ≤ value A w + 1 := by decide
theorem edge_row20 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 20) (point w) → value A 20 ≤ value A w + 1 := by decide
theorem edge_row21 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 21) (point w) → value A 21 ≤ value A w + 1 := by decide
theorem edge_row22 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 22) (point w) → value A 22 ≤ value A w + 1 := by decide
theorem edge_row23 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 23) (point w) → value A 23 ≤ value A w + 1 := by decide
theorem edge_row24 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 24) (point w) → value A 24 ≤ value A w + 1 := by decide
theorem edge_row25 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 25) (point w) → value A 25 ≤ value A w + 1 := by decide
theorem edge_row26 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 26) (point w) → value A 26 ≤ value A w + 1 := by decide
theorem edge_row27 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 27) (point w) → value A 27 ≤ value A w + 1 := by decide
theorem edge_row28 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 28) (point w) → value A 28 ≤ value A w + 1 := by decide
theorem edge_row29 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 29) (point w) → value A 29 ≤ value A w + 1 := by decide
theorem edge_row30 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 30) (point w) → value A 30 ≤ value A w + 1 := by decide
theorem edge_row31 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 31) (point w) → value A 31 ≤ value A w + 1 := by decide
theorem edge_row32 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 32) (point w) → value A 32 ≤ value A w + 1 := by decide
theorem edge_row33 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 33) (point w) → value A 33 ≤ value A w + 1 := by decide
theorem edge_row34 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 34) (point w) → value A 34 ≤ value A w + 1 := by decide
theorem edge_row35 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 35) (point w) → value A 35 ≤ value A w + 1 := by decide
theorem edge_row36 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 36) (point w) → value A 36 ≤ value A w + 1 := by decide
theorem edge_row37 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 37) (point w) → value A 37 ≤ value A w + 1 := by decide
theorem edge_row38 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 38) (point w) → value A 38 ≤ value A w + 1 := by decide
theorem edge_row39 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 39) (point w) → value A 39 ≤ value A w + 1 := by decide
theorem edge_row40 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 40) (point w) → value A 40 ≤ value A w + 1 := by decide
theorem edge_row41 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 41) (point w) → value A 41 ≤ value A w + 1 := by decide
theorem edge_row42 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 42) (point w) → value A 42 ≤ value A w + 1 := by decide
theorem edge_row43 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 43) (point w) → value A 43 ≤ value A w + 1 := by decide
theorem edge_row44 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 44) (point w) → value A 44 ≤ value A w + 1 := by decide
theorem edge_row45 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 45) (point w) → value A 45 ≤ value A w + 1 := by decide
theorem edge_row46 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 46) (point w) → value A 46 ≤ value A w + 1 := by decide
theorem edge_row47 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 47) (point w) → value A 47 ≤ value A w + 1 := by decide
theorem edge_row48 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 48) (point w) → value A 48 ≤ value A w + 1 := by decide
theorem edge_row49 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 49) (point w) → value A 49 ≤ value A w + 1 := by decide
theorem edge_row50 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 50) (point w) → value A 50 ≤ value A w + 1 := by decide
theorem edge_row51 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 51) (point w) → value A 51 ≤ value A w + 1 := by decide
theorem edge_row52 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 52) (point w) → value A 52 ≤ value A w + 1 := by decide
theorem edge_row53 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 53) (point w) → value A 53 ≤ value A w + 1 := by decide
theorem edge_row54 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 54) (point w) → value A 54 ≤ value A w + 1 := by decide
theorem edge_row55 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 55) (point w) → value A 55 ≤ value A w + 1 := by decide
theorem edge_row56 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 56) (point w) → value A 56 ≤ value A w + 1 := by decide
theorem edge_row57 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 57) (point w) → value A 57 ≤ value A w + 1 := by decide
theorem edge_row58 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 58) (point w) → value A 58 ≤ value A w + 1 := by decide
theorem edge_row59 : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point 59) (point w) → value A 59 ≤ value A w + 1 := by decide
theorem edge_check : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powerset, A.Nonempty → ∀ z : Fin 60, z ∈ Finset.univ → ∀ w : Fin 60, w ∈ Finset.univ →
 Adj (point z) (point w) → value A z ≤ value A w + 1 := by
  intro A hA hn z _ w hw ha
  fin_cases z
  · exact edge_row0 A hA hn w hw ha
  · exact edge_row1 A hA hn w hw ha
  · exact edge_row2 A hA hn w hw ha
  · exact edge_row3 A hA hn w hw ha
  · exact edge_row4 A hA hn w hw ha
  · exact edge_row5 A hA hn w hw ha
  · exact edge_row6 A hA hn w hw ha
  · exact edge_row7 A hA hn w hw ha
  · exact edge_row8 A hA hn w hw ha
  · exact edge_row9 A hA hn w hw ha
  · exact edge_row10 A hA hn w hw ha
  · exact edge_row11 A hA hn w hw ha
  · exact edge_row12 A hA hn w hw ha
  · exact edge_row13 A hA hn w hw ha
  · exact edge_row14 A hA hn w hw ha
  · exact edge_row15 A hA hn w hw ha
  · exact edge_row16 A hA hn w hw ha
  · exact edge_row17 A hA hn w hw ha
  · exact edge_row18 A hA hn w hw ha
  · exact edge_row19 A hA hn w hw ha
  · exact edge_row20 A hA hn w hw ha
  · exact edge_row21 A hA hn w hw ha
  · exact edge_row22 A hA hn w hw ha
  · exact edge_row23 A hA hn w hw ha
  · exact edge_row24 A hA hn w hw ha
  · exact edge_row25 A hA hn w hw ha
  · exact edge_row26 A hA hn w hw ha
  · exact edge_row27 A hA hn w hw ha
  · exact edge_row28 A hA hn w hw ha
  · exact edge_row29 A hA hn w hw ha
  · exact edge_row30 A hA hn w hw ha
  · exact edge_row31 A hA hn w hw ha
  · exact edge_row32 A hA hn w hw ha
  · exact edge_row33 A hA hn w hw ha
  · exact edge_row34 A hA hn w hw ha
  · exact edge_row35 A hA hn w hw ha
  · exact edge_row36 A hA hn w hw ha
  · exact edge_row37 A hA hn w hw ha
  · exact edge_row38 A hA hn w hw ha
  · exact edge_row39 A hA hn w hw ha
  · exact edge_row40 A hA hn w hw ha
  · exact edge_row41 A hA hn w hw ha
  · exact edge_row42 A hA hn w hw ha
  · exact edge_row43 A hA hn w hw ha
  · exact edge_row44 A hA hn w hw ha
  · exact edge_row45 A hA hn w hw ha
  · exact edge_row46 A hA hn w hw ha
  · exact edge_row47 A hA hn w hw ha
  · exact edge_row48 A hA hn w hw ha
  · exact edge_row49 A hA hn w hw ha
  · exact edge_row50 A hA hn w hw ha
  · exact edge_row51 A hA hn w hw ha
  · exact edge_row52 A hA hn w hw ha
  · exact edge_row53 A hA hn w hw ha
  · exact edge_row54 A hA hn w hw ha
  · exact edge_row55 A hA hn w hw ha
  · exact edge_row56 A hA hn w hw ha
  · exact edge_row57 A hA hn w hw ha
  · exact edge_row58 A hA hn w hw ha
  · exact edge_row59 A hA hn w hw ha
end Polyomino57.Diagonal.FiniteProof.Small
