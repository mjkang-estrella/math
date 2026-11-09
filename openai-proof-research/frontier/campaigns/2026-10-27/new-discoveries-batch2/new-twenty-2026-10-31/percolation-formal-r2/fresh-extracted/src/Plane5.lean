import Definitions
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
def lineMasks : List Nat := [2113929216, 50872848, 37884036, 42213640, 35719234, 1106247680, 537989392, 135531012, 269631560, 68690050, 1073773568, 270795920, 545784900, 71370248, 151127298, 1074757632, 138453072, 69255428, 553683080, 276861442, 1073742816, 75630640, 285286436, 136843304, 541343778, 1073741855, 539107841, 142688385, 273156353, 84152385, 34636833]
def incidence (p l : Points 5) : Bool := (lineMasks[l.val]!).testBit p.val
def vx (p : Points 5) : Nat := if p.val < 25 then 1 else 0
def vy (p : Points 5) : Nat := if p.val < 25 then p.val / 5 else if p.val < 30 then 1 else 0
def vz (p : Points 5) : Nat := if p.val < 25 then p.val % 5 else if p.val < 30 then p.val-25 else 1
def dotZero (p l : Points 5) : Bool :=
  decide ((vx p * vx l + vy p * vy l + vz p * vz l) % 5 = 0)
theorem incidence_dot : ∀ p l, incidence p l = dotZero p l := by decide
theorem pg_line_degree : ∀ l, card (List.finRange (size 5)) (fun p => incidence p l) = 6 := by decide
theorem pg_point_degree : ∀ p, card (List.finRange (size 5)) (fun l => incidence p l) = 6 := by decide
theorem pg_join : ∀ p p', p ≠ p' → card (List.finRange (size 5)) (fun l => incidence p l && incidence p' l) = 1 := by decide
theorem pg_meet : ∀ l l', l ≠ l' → card (List.finRange (size 5)) (fun p => incidence p l && incidence p l') = 1 := by decide
def PG5 : Plane 5 where
  nontrivial := by decide
  inc := incidence
  line_degree := pg_line_degree
  point_degree := pg_point_degree
  join := pg_join
  meet := pg_meet
  quadrangle := ⟨0,25,30,6, by decide⟩
-- An explicit quadrangle also verifies nondegeneracy without relying on counting arguments.
theorem quadrangle : ∀ l : Points 5,
    card ([0,25,30,6] : List (Points 5)) (fun p => incidence p l) ≤ 2 := by decide
end Percolation
