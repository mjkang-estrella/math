import R9_6_0Rows0
import R9_6_0Rows1
import R9_6_0Rows2
import R9_6_0Rows3
import R9_6_0Rows4
import R9_6_0Rows5
import R9_6_0Rows6
import R9_6_0Rows7
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_6_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def point (i : Fin 35) : GridPoint := (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0,0) else (1,-1)) else (if (i.val-2) < 1 then (2,-2) else (3,-3))) else (if (i.val-4) < 2 then (if (i.val-4) < 1 then (1,0) else (2,-1)) else (if ((i.val-4)-2) < 1 then (3,-2) else (1,1)))) else (if (i.val-8) < 4 then (if (i.val-8) < 2 then (if (i.val-8) < 1 then (2,0) else (3,-1)) else (if ((i.val-8)-2) < 1 then (4,-2) else (2,1))) else (if ((i.val-8)-4) < 2 then (if ((i.val-8)-4) < 1 then (3,0) else (4,-1)) else (if (((i.val-8)-4)-2) < 1 then (2,2) else (if ((((i.val-8)-4)-2)-1) < 1 then (3,1) else (4,0)))))) else (if (i.val-17) < 9 then (if (i.val-17) < 4 then (if (i.val-17) < 2 then (if (i.val-17) < 1 then (5,-1) else (3,2)) else (if ((i.val-17)-2) < 1 then (4,1) else (5,0))) else (if ((i.val-17)-4) < 2 then (if ((i.val-17)-4) < 1 then (3,3) else (4,2)) else (if (((i.val-17)-4)-2) < 1 then (5,1) else (if ((((i.val-17)-4)-2)-1) < 1 then (6,0) else (4,3))))) else (if ((i.val-17)-9) < 4 then (if ((i.val-17)-9) < 2 then (if ((i.val-17)-9) < 1 then (5,2) else (6,1)) else (if (((i.val-17)-9)-2) < 1 then (4,4) else (5,3))) else (if (((i.val-17)-9)-4) < 2 then (if (((i.val-17)-9)-4) < 1 then (6,2) else (7,1)) else (if ((((i.val-17)-9)-4)-2) < 1 then (5,4) else (if (((((i.val-17)-9)-4)-2)-1) < 1 then (6,3) else (7,2)))))))
def group (i : ℕ) : Finset GridPoint := (if i < 4 then (if i < 2 then (if i < 1 then {(0,0),(1,-1),(2,-2),(3,-3)} else {(0,0),(1,1),(2,2),(3,3),(4,4)}) else (if (i-2) < 1 then {(1,-1),(5,-1),(5,3)} else {(2,-2),(2,2),(6,2)})) else (if (i-4) < 2 then (if (i-4) < 1 then {(3,-3),(4,-2),(5,-1),(6,0),(7,1)} else {(1,0),(5,0),(5,4)}) else (if ((i-4)-2) < 1 then {(2,-1),(6,3)} else (if (((i-4)-2)-1) < 1 then {(3,-2),(3,2),(7,2)} else {(5,4),(6,3),(7,2)}))))
def table (m : ℕ) : ℕ := (if (m/64) < 4 then (if (m/64) < 2 then (if (m/64) < 1 then (rows0 (m-0)) else (rows1 (m-64))) else (if ((m/64)-2) < 1 then (rows2 (m-128)) else (rows3 (m-192)))) else (if ((m/64)-4) < 2 then (if ((m/64)-4) < 1 then (rows4 (m-256)) else (rows5 (m-320))) else (if (((m/64)-4)-2) < 1 then (rows6 (m-384)) else (rows7 (m-448)))))
def value (A : Finset ℕ) (v : Fin 35) : ℕ := digit (rowOf 9 table A) v.val

end R9_6_0
