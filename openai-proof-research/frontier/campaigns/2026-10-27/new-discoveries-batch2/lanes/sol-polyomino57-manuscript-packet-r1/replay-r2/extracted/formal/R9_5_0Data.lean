import R9_5_0Rows0
import R9_5_0Rows1
import R9_5_0Rows2
import R9_5_0Rows3
import R9_5_0Rows4
import R9_5_0Rows5
import R9_5_0Rows6
import R9_5_0Rows7
import R9_5_0Rows8
import R9_5_0Rows9
import R9_5_0Rows10
import R9_5_0Rows11
import R9_5_0Rows12
import R9_5_0Rows13
import R9_5_0Rows14
import R9_5_0Rows15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
def point (i : Fin 30) : GridPoint := (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (0,0) else (if (i.val-1) < 1 then (1,-1) else (2,-2))) else (if (i.val-3) < 2 then (if (i.val-3) < 1 then (1,0) else (2,-1)) else (if ((i.val-3)-2) < 1 then (3,-2) else (1,1)))) else (if (i.val-7) < 4 then (if (i.val-7) < 2 then (if (i.val-7) < 1 then (2,0) else (3,-1)) else (if ((i.val-7)-2) < 1 then (2,1) else (3,0))) else (if ((i.val-7)-4) < 2 then (if ((i.val-7)-4) < 1 then (4,-1) else (2,2)) else (if (((i.val-7)-4)-2) < 1 then (3,1) else (4,0))))) else (if (i.val-15) < 7 then (if (i.val-15) < 3 then (if (i.val-15) < 1 then (3,2) else (if ((i.val-15)-1) < 1 then (4,1) else (5,0))) else (if ((i.val-15)-3) < 2 then (if ((i.val-15)-3) < 1 then (3,3) else (4,2)) else (if (((i.val-15)-3)-2) < 1 then (5,1) else (4,3)))) else (if ((i.val-15)-7) < 4 then (if ((i.val-15)-7) < 2 then (if ((i.val-15)-7) < 1 then (5,2) else (6,1)) else (if (((i.val-15)-7)-2) < 1 then (4,4) else (5,3))) else (if (((i.val-15)-7)-4) < 2 then (if (((i.val-15)-7)-4) < 1 then (6,2) else (5,4)) else (if ((((i.val-15)-7)-4)-2) < 1 then (6,3) else (7,2))))))
def group (i : ℕ) : Finset GridPoint := (if i < 5 then (if i < 2 then (if i < 1 then {(0,0),(1,-1),(2,-2)} else {(0,0),(1,1),(2,2),(3,3),(4,4)}) else (if (i-2) < 1 then {(0,0),(4,0),(4,4)} else (if ((i-2)-1) < 1 then {(1,-1),(5,3)} else {(2,-2),(2,2),(6,2)}))) else (if (i-5) < 2 then (if (i-5) < 1 then {(1,0),(5,0),(5,4)} else {(2,-1),(6,3)}) else (if ((i-5)-2) < 1 then {(3,-2),(4,-1),(5,0),(6,1),(7,2)} else (if (((i-5)-2)-1) < 1 then {(3,-2),(3,2),(7,2)} else {(5,4),(6,3),(7,2)}))))
def table (m : ℕ) : ℕ := (if (m/64) < 8 then (if (m/64) < 4 then (if (m/64) < 2 then (if (m/64) < 1 then (rows0 (m-0)) else (rows1 (m-64))) else (if ((m/64)-2) < 1 then (rows2 (m-128)) else (rows3 (m-192)))) else (if ((m/64)-4) < 2 then (if ((m/64)-4) < 1 then (rows4 (m-256)) else (rows5 (m-320))) else (if (((m/64)-4)-2) < 1 then (rows6 (m-384)) else (rows7 (m-448))))) else (if ((m/64)-8) < 4 then (if ((m/64)-8) < 2 then (if ((m/64)-8) < 1 then (rows8 (m-512)) else (rows9 (m-576))) else (if (((m/64)-8)-2) < 1 then (rows10 (m-640)) else (rows11 (m-704)))) else (if (((m/64)-8)-4) < 2 then (if (((m/64)-8)-4) < 1 then (rows12 (m-768)) else (rows13 (m-832))) else (if ((((m/64)-8)-4)-2) < 1 then (rows14 (m-896)) else (rows15 (m-960))))))
def value (A : Finset ℕ) (v : Fin 30) : ℕ := digit (rowOf 10 table A) v.val

end R9_5_0
